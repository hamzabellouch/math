import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import OAI.Computability.BinPacking.Packing.FractionWidth

namespace OAI

noncomputable section

section

open scoped BigOperators
open Set

namespace BinPackingGap.FractionalCover

variable {I C : Type*} [Fintype C]

theorem objective_nonneg {w : C → ℝ} (hw : ∀ c, 0 ≤ w c) :
    0 ≤ objective w :=
  Finset.sum_nonneg fun c _ => hw c

theorem coordinate_le_objective {w : C → ℝ} (hw : ∀ c, 0 ≤ w c) (c : C) :
    w c ≤ objective w :=
  Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ c)

theorem objectiveSet_nonempty {a : C → I → ℝ} {d : I → ℝ}
    (hfeas : ∃ w, Feasible a d w) : (objectiveSet a d).Nonempty := by
  obtain ⟨w, hw⟩ := hfeas
  exact ⟨objective w, w, hw, rfl⟩

theorem objectiveSet_bddBelow (a : C → I → ℝ) (d : I → ℝ) :
    BddBelow (objectiveSet a d) := by
  refine ⟨0, ?_⟩
  rintro v ⟨w, hw, rfl⟩
  exact objective_nonneg hw.1

theorem value_le_of_feasible {a : C → I → ℝ} {d : I → ℝ} {w : C → ℝ}
    (hw : Feasible a d w) : value a d ≤ objective w :=
  csInf_le (objectiveSet_bddBelow a d) ⟨w, hw, rfl⟩

theorem le_value_of_lower_bound {a : C → I → ℝ} {d : I → ℝ} {b : ℝ}
    (hfeas : ∃ w, Feasible a d w)
    (hb : ∀ w, Feasible a d w → b ≤ objective w) : b ≤ value a d := by
  apply le_csInf (objectiveSet_nonempty hfeas)
  rintro v ⟨w, hw, rfl⟩
  exact hb w hw

theorem value_nonneg {a : C → I → ℝ} {d : I → ℝ}
    (hfeas : ∃ w, Feasible a d w) : 0 ≤ value a d :=
  le_value_of_lower_bound hfeas fun _ hw => objective_nonneg hw.1

theorem continuous_objective : Continuous (objective (C := C)) := by
  unfold objective
  exact continuous_finsetSum _ fun c _ => continuous_apply c

theorem continuous_coverage (a : C → I → ℝ) (i : I) :
    Continuous (fun w : C → ℝ => ∑ c, a c i * w c) :=
  continuous_finsetSum _ fun c _ => continuous_const.mul (continuous_apply c)

theorem isClosed_feasible (a : C → I → ℝ) (d : I → ℝ) :
    IsClosed {w | Feasible a d w} := by
  have hn : IsClosed {w : C → ℝ | ∀ c, 0 ≤ w c} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun c => isClosed_le continuous_const (continuous_apply c)
  have hd : IsClosed {w : C → ℝ | ∀ i, d i ≤ ∑ c, a c i * w c} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_coverage a i)
  exact hn.inter hd

theorem isCompact_sublevel (a : C → I → ℝ) (d : I → ℝ) (b : ℝ) :
    IsCompact {w | Feasible a d w ∧ objective w ≤ b} := by
  have hc : IsClosed {w | Feasible a d w ∧ objective w ≤ b} :=
    (isClosed_feasible a d).inter (isClosed_le continuous_objective continuous_const)
  apply (isCompact_Icc (a := (0 : C → ℝ)) (b := fun _ => b)).of_isClosed_subset hc
  intro w hw
  exact ⟨hw.1.1, fun c => (coordinate_le_objective hw.1.1 c).trans hw.2⟩

theorem exists_minimum {a : C → I → ℝ} {d : I → ℝ}
    (hfeas : ∃ w, Feasible a d w) :
    ∃ w, Feasible a d w ∧ ∀ v, Feasible a d v → objective w ≤ objective v := by
  obtain ⟨w₀, hw₀⟩ := hfeas
  obtain ⟨w, hw, hmin⟩ :=
    (isCompact_sublevel a d (objective w₀)).exists_isMinOn
      ⟨w₀, hw₀, le_rfl⟩ continuous_objective.continuousOn
  refine ⟨w, hw.1, fun v hv => ?_⟩
  rcases le_total (objective v) (objective w₀) with h | h
  · exact hmin ⟨hv, h⟩
  · exact hw.2.trans h

theorem exists_minimizer {a : C → I → ℝ} {d : I → ℝ}
    (hfeas : ∃ w, Feasible a d w) :
    ∃ w, Feasible a d w ∧ objective w = value a d := by
  obtain ⟨w, hw, hmin⟩ := exists_minimum hfeas
  exact ⟨w, hw, le_antisymm (le_value_of_lower_bound ⟨w, hw⟩ hmin)
    (value_le_of_feasible hw)⟩

theorem value_eq_of_feasible_of_lower_bound {a : C → I → ℝ} {d : I → ℝ}
    {w : C → ℝ} {b : ℝ} (hw : Feasible a d w) (hwobj : objective w = b)
    (hb : ∀ v, Feasible a d v → b ≤ objective v) : value a d = b := by
  apply le_antisymm
  · exact hwobj ▸ value_le_of_feasible hw
  · exact le_value_of_lower_bound ⟨w, hw⟩ hb

theorem sum_demand_le_mul_objective [Fintype I] {a : C → I → ℝ} {d : I → ℝ}
    {w : C → ℝ} {K : ℝ} (hw : Feasible a d w)
    (hcol : ∀ c, (∑ i, a c i) ≤ K) : (∑ i, d i) ≤ K * objective w := by
  calc
    (∑ i, d i) ≤ ∑ i, ∑ c, a c i * w c :=
      Finset.sum_le_sum fun i _ => hw.2 i
    _ = ∑ c, (∑ i, a c i) * w c := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ ∑ c, K * w c :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (hcol c) (hw.1 c)
    _ = K * objective w := (Finset.mul_sum _ _ _).symm

theorem sum_demand_le_mul_value [Fintype I] {a : C → I → ℝ} {d : I → ℝ} {K : ℝ}
    (hfeas : ∃ w, Feasible a d w) (hcol : ∀ c, (∑ i, a c i) ≤ K) :
    (∑ i, d i) ≤ K * value a d := by
  obtain ⟨w, hw, hwobj⟩ := exists_minimizer hfeas
  rw [← hwobj]
  exact sum_demand_le_mul_objective hw hcol

variable {J : Type*} [Fintype J]

def pushforward (f : J → C) (mass : J → ℝ) : C → ℝ := by
  classical
  exact fun c => ∑ j, if f j = c then mass j else 0

omit [Fintype C] in
theorem pushforward_nonneg (f : J → C) {mass : J → ℝ}
    (hmass : ∀ j, 0 ≤ mass j) : ∀ c, 0 ≤ pushforward f mass c := by
  classical
  intro c
  exact Finset.sum_nonneg fun j _ => by
    by_cases h : f j = c
    · simpa [h] using hmass j
    · simp [h]

theorem objective_pushforward (f : J → C) (mass : J → ℝ) :
    objective (pushforward f mass) = objective mass := by
  classical
  unfold objective pushforward
  rw [Finset.sum_comm]
  simp

theorem coverage_pushforward (a : C → I → ℝ) (f : J → C) (mass : J → ℝ) (i : I) :
    (∑ c, a c i * pushforward f mass c) = ∑ j, a (f j) i * mass j := by
  classical
  simp only [pushforward, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

theorem feasible_pushforward {a : C → I → ℝ} {d : I → ℝ}
    (f : J → C) {mass : J → ℝ}
    (hmass : Feasible (fun j i => a (f j) i) d mass) :
    Feasible a d (pushforward f mass) := by
  refine ⟨pushforward_nonneg f hmass.1, fun i => ?_⟩
  rw [coverage_pushforward]
  exact hmass.2 i

end BinPackingGap.FractionalCover

end

namespace BinPackingGap

open scoped BigOperators

namespace NumericalSize

variable {I : Instance}

theorem le_one (s : NumericalSize I) : s.val ≤ 1 := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp s.property
  rw [← hi]
  exact I.size_le_one i

def ofItem (i : I.Item) : NumericalSize I :=
  ⟨I.size i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

@[simp] theorem ofItem_val (i : I.Item) : (ofItem i).val = I.size i := rfl

end NumericalSize

namespace TypeConfiguration

variable {I : Instance}

def empty (I : Instance) : TypeConfiguration I := ⟨fun _ => 0, by simp⟩

instance : Nonempty (TypeConfiguration I) := ⟨empty I⟩

def ofIndividual (H : IndividualConfiguration I) : TypeConfiguration I where
  val s := (H.val.filter fun i => I.size i = s.val).card
  property := by
    classical
    have hsum : (∑ s : NumericalSize I,
        s.val * ((H.val.filter fun i => I.size i = s.val).card : ℚ)) =
        ∑ i ∈ H.val, I.size i := by
      calc
        _ = ∑ s : NumericalSize I, ∑ i ∈ H.val,
            if I.size i = s.val then I.size i else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          rw [← Finset.sum_filter]
          rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
          simp [mul_comm]
        _ = ∑ i ∈ H.val, ∑ s : NumericalSize I,
            if I.size i = s.val then I.size i else 0 := by rw [Finset.sum_comm]
        _ = ∑ i ∈ H.val, I.size i := by
          apply Finset.sum_congr rfl
          intro i _
          have heq : ∀ s : NumericalSize I, I.size i = s.val ↔ NumericalSize.ofItem i = s := by
            intro s
            constructor
            · intro h
              exact Subtype.ext h
            · intro h
              exact congrArg Subtype.val h
          simp [heq]
    rw [hsum]
    exact H.property

@[simp] theorem ofIndividual_count (H : IndividualConfiguration I) (s : NumericalSize I) :
    (ofIndividual H).val s = (H.val.filter fun i => I.size i = s.val).card := rfl

theorem card_le_five (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    (c : TypeConfiguration I) : (∑ s, c.val s) ≤ 5 := by
  classical
  by_contra h
  have hc : 6 ≤ ∑ s, c.val s := by omega
  have hcq : (6 : ℚ) ≤ ∑ s, (c.val s : ℚ) := by exact_mod_cast hc
  have hsize : ∀ s : NumericalSize I, (1 / 6 : ℚ) < s.val := by
    intro s
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp s.property
    simpa [hi] using hlarge i
  have hnz : ∃ s : NumericalSize I, 0 < c.val s := by
    by_contra hn
    push Not at hn
    have hz : ∀ s, c.val s = 0 := fun s => Nat.eq_zero_of_le_zero (hn s)
    simp [hz] at hc
  obtain ⟨s, hs⟩ := hnz
  have hstrict : (∑ t : NumericalSize I, (1 / 6 : ℚ) * (c.val t : ℚ)) <
      ∑ t : NumericalSize I, t.val * (c.val t : ℚ) := by
    apply Finset.sum_lt_sum
    · intro t _
      exact mul_le_mul_of_nonneg_right (le_of_lt (hsize t)) (Nat.cast_nonneg _)
    · refine ⟨s, Finset.mem_univ _, ?_⟩
      exact mul_lt_mul_of_pos_right (hsize s) (by exact_mod_cast hs)
  rw [← Finset.mul_sum] at hstrict
  have hcap := c.property
  linarith

end TypeConfiguration

theorem sum_type_multiplicity (I : Instance) :
    ∑ s : NumericalSize I, s.multiplicity = I.n := by
  classical
  simp only [NumericalSize.multiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    (∑ i : I.Item, ∑ s : NumericalSize I, if I.size i = s.val then 1 else 0) =
        ∑ _i : I.Item, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      have heq : ∀ s : NumericalSize I, I.size i = s.val ↔ NumericalSize.ofItem i = s := by
        intro s
        constructor
        · intro h
          exact Subtype.ext h
        · intro h
          exact congrArg Subtype.val h
      simp [heq]
    _ = I.n := by simp [Instance.Item]

def IndividualFeasible (I : Instance) (w : IndividualConfiguration I → ℝ) : Prop :=
  FractionalCover.Feasible (individualMatrix I) (fun _ => 1) w

def TypeFeasible (I : Instance) (w : TypeConfiguration I → ℝ) : Prop :=
  FractionalCover.Feasible (typeMatrix I) (fun s => (s.multiplicity : ℝ)) w

theorem individualMatrix_sum (I : Instance) (H : IndividualConfiguration I) :
    ∑ i, individualMatrix I H i = (H.val.card : ℝ) := by
  classical
  simp [individualMatrix]

theorem typeMatrix_sum (I : Instance) (c : TypeConfiguration I) :
    ∑ s, typeMatrix I c s = ((∑ s, c.val s : ℕ) : ℝ) := by
  simp [typeMatrix]

def singletonWeights (I : Instance) : IndividualConfiguration I → ℝ :=
  FractionalCover.pushforward IndividualConfiguration.singleton (fun _ : I.Item => 1)

theorem singletonWeights_feasible (I : Instance) : IndividualFeasible I (singletonWeights I) := by
  classical
  apply FractionalCover.feasible_pushforward
  constructor
  · intro i
    norm_num
  · intro i
    simp [individualMatrix, IndividualConfiguration.singleton]

theorem singletonWeights_objective (I : Instance) :
    FractionalCover.objective (singletonWeights I) = (I.n : ℝ) := by
  rw [singletonWeights, FractionalCover.objective_pushforward]
  simp [FractionalCover.objective, Instance.Item]

theorem individualLP_attained (I : Instance) :
    ∃ w, IndividualFeasible I w ∧ FractionalCover.objective w = individualLP I :=
  FractionalCover.exists_minimizer ⟨singletonWeights I, singletonWeights_feasible I⟩

theorem individualLP_nonneg (I : Instance) : 0 ≤ individualLP I :=
  FractionalCover.value_nonneg ⟨singletonWeights I, singletonWeights_feasible I⟩

theorem individualLP_le_n (I : Instance) : individualLP I ≤ I.n := by
  rw [← singletonWeights_objective I]
  exact FractionalCover.value_le_of_feasible (singletonWeights_feasible I)

theorem typeMatrix_ofIndividual (I : Instance) (H : IndividualConfiguration I)
    (s : NumericalSize I) :
    typeMatrix I (TypeConfiguration.ofIndividual H) s =
      ∑ i : I.Item, if I.size i = s.val then individualMatrix I H i else 0 := by
  classical
  change ((H.val.filter fun i => I.size i = s.val).card : ℝ) = _
  calc
    _ = ∑ i ∈ H.val, if I.size i = s.val then (1 : ℝ) else 0 := by
      simp
    _ = ∑ i ∈ H.val, if I.size i = s.val then individualMatrix I H i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [individualMatrix, hi]
    _ = ∑ i : I.Item, if I.size i = s.val then individualMatrix I H i else 0 := by
      apply Finset.sum_subset (Finset.subset_univ H.val)
      intro i _ hi
      simp [individualMatrix, hi]

def projectWeights (I : Instance) (w : IndividualConfiguration I → ℝ) :
    TypeConfiguration I → ℝ :=
  FractionalCover.pushforward TypeConfiguration.ofIndividual w

theorem projectWeights_objective (I : Instance) (w : IndividualConfiguration I → ℝ) :
    FractionalCover.objective (projectWeights I w) = FractionalCover.objective w :=
  FractionalCover.objective_pushforward _ _

theorem projectWeights_feasible (I : Instance) {w : IndividualConfiguration I → ℝ}
    (hw : IndividualFeasible I w) : TypeFeasible I (projectWeights I w) := by
  classical
  apply FractionalCover.feasible_pushforward
  refine ⟨hw.1, fun s => ?_⟩
  have hcoverage := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    show (if I.size i = s.val then (1 : ℝ) else 0) ≤
      if I.size i = s.val then ∑ H, individualMatrix I H i * w H else 0 by
        split_ifs
        · exact hw.2 i
        · rfl)
  have hleft : (∑ i : I.Item, if I.size i = s.val then (1 : ℝ) else 0) =
      s.multiplicity := by
    simp [NumericalSize.multiplicity]
  have hright :
      (∑ i : I.Item, if I.size i = s.val then ∑ H, individualMatrix I H i * w H else 0) =
      ∑ H, typeMatrix I (TypeConfiguration.ofIndividual H) s * w H := by
    simp_rw [typeMatrix_ofIndividual, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with h
    · simp
    · simp
  simpa only [hleft, hright] using hcoverage

theorem typeLP_attained (I : Instance) :
    ∃ w, TypeFeasible I w ∧ FractionalCover.objective w = typeLP I :=
  FractionalCover.exists_minimizer
    ⟨projectWeights I (singletonWeights I), projectWeights_feasible I (singletonWeights_feasible I)⟩

theorem typeLP_nonneg (I : Instance) : 0 ≤ typeLP I :=
  FractionalCover.value_nonneg
    ⟨projectWeights I (singletonWeights I), projectWeights_feasible I (singletonWeights_feasible I)⟩

theorem typeLP_le_individualLP (I : Instance) : typeLP I ≤ individualLP I := by
  obtain ⟨w, hw, hobj⟩ := individualLP_attained I
  calc
    typeLP I ≤ FractionalCover.objective (projectWeights I w) :=
      FractionalCover.value_le_of_feasible (projectWeights_feasible I hw)
    _ = individualLP I := (projectWeights_objective I w).trans hobj

theorem individualLP_eq_zero_of_n_eq_zero (I : Instance) (h : I.n = 0) :
    individualLP I = 0 := by
  have hle := individualLP_le_n I
  rw [h, Nat.cast_zero] at hle
  exact le_antisymm hle (individualLP_nonneg I)

theorem typeLP_eq_zero_of_n_eq_zero (I : Instance) (h : I.n = 0) : typeLP I = 0 := by
  apply le_antisymm
  · simpa [individualLP_eq_zero_of_n_eq_zero I h] using typeLP_le_individualLP I
  · exact typeLP_nonneg I

namespace Packing

def fractionalWeights {I : Instance} {b : ℕ} (p : Packing I b) :
    IndividualConfiguration I → ℝ :=
  FractionalCover.pushforward p.configuration (fun _ : Fin b => 1)

theorem fractionalWeights_feasible {I : Instance} {b : ℕ} (p : Packing I b) :
    IndividualFeasible I p.fractionalWeights := by
  classical
  apply FractionalCover.feasible_pushforward
  constructor
  · intro j
    norm_num
  · intro i
    simp [individualMatrix, configuration]

theorem fractionalWeights_objective {I : Instance} {b : ℕ} (p : Packing I b) :
    FractionalCover.objective p.fractionalWeights = (b : ℝ) := by
  rw [fractionalWeights, FractionalCover.objective_pushforward]
  simp [FractionalCover.objective]

end Packing

theorem individualLP_le_opt (I : Instance) : individualLP I ≤ (opt I : ℝ) := by
  obtain ⟨p⟩ := opt_attained I
  rw [← p.fractionalWeights_objective]
  exact FractionalCover.value_le_of_feasible p.fractionalWeights_feasible

theorem typeLP_le_opt (I : Instance) : typeLP I ≤ (opt I : ℝ) :=
  (typeLP_le_individualLP I).trans (individualLP_le_opt I)

theorem n_le_five_mul_individual_objective (I : Instance)
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    {w : IndividualConfiguration I → ℝ} (hw : IndividualFeasible I w) :
    (I.n : ℝ) ≤ 5 * FractionalCover.objective w := by
  have hcol : ∀ H : IndividualConfiguration I, (∑ i, individualMatrix I H i) ≤ 5 := by
    intro H
    rw [individualMatrix_sum]
    exact_mod_cast H.card_le_five hlarge
  simpa [Instance.Item] using FractionalCover.sum_demand_le_mul_objective hw hcol

theorem n_le_five_mul_type_objective (I : Instance)
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    {w : TypeConfiguration I → ℝ} (hw : TypeFeasible I w) :
    (I.n : ℝ) ≤ 5 * FractionalCover.objective w := by
  have hcol : ∀ c : TypeConfiguration I, (∑ s, typeMatrix I c s) ≤ 5 := by
    intro c
    rw [typeMatrix_sum]
    exact_mod_cast c.card_le_five hlarge
  have h := FractionalCover.sum_demand_le_mul_objective hw hcol
  have hdem : (∑ s : NumericalSize I, (s.multiplicity : ℝ)) = I.n := by
    rw [← Nat.cast_sum, sum_type_multiplicity]
  simpa only [hdem] using h

theorem n_le_five_mul_individualLP (I : Instance)
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i) : (I.n : ℝ) ≤ 5 * individualLP I := by
  obtain ⟨w, hw, hobj⟩ := individualLP_attained I
  rw [← hobj]
  exact n_le_five_mul_individual_objective I hlarge hw

theorem n_le_five_mul_typeLP (I : Instance)
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i) : (I.n : ℝ) ≤ 5 * typeLP I := by
  obtain ⟨w, hw, hobj⟩ := typeLP_attained I
  rw [← hobj]
  exact n_le_five_mul_type_objective I hlarge hw

theorem bothLP_eq_of_physical_witness (I : Instance) (B : ℕ)
    (hcount : I.n = 5 * B) (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    (w : IndividualConfiguration I → ℝ) (hw : IndividualFeasible I w)
    (hobj : FractionalCover.objective w = (B : ℝ)) :
    individualLP I = (B : ℝ) ∧ typeLP I = (B : ℝ) := by
  have hcountR : (I.n : ℝ) = 5 * (B : ℝ) := by exact_mod_cast hcount
  have hilow := n_le_five_mul_individualLP I hlarge
  have htlow := n_le_five_mul_typeLP I hlarge
  have hiup : individualLP I ≤ (B : ℝ) := by
    rw [← hobj]
    exact FractionalCover.value_le_of_feasible hw
  have htup : typeLP I ≤ (B : ℝ) := (typeLP_le_individualLP I).trans hiup
  constructor <;> linarith

end BinPackingGap

end

end OAI
