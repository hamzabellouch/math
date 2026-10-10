import Mathlib
import OAI.NumberTheory.Jacobsthal.Sieve.ActualCofactorCellData

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseCells
attribute [local instance] Classical.decEq

noncomputable def labelFiber {ι : Type*} (Q : Finset ℕ) (label : ℕ → ι) (i : ι) : Finset ℕ :=
  Q.filter (fun q => label q = i)

theorem mem_labelFiber {ι : Type*} (Q : Finset ℕ) (label : ℕ → ι) (i : ι) (q : ℕ) :
    q ∈ labelFiber Q label i ↔ q ∈ Q ∧ label q = i := Finset.mem_filter

theorem labelFiber_subset {ι : Type*} (Q : Finset ℕ) (label : ℕ → ι) (i : ι) :
    labelFiber Q label i ⊆ Q := Finset.filter_subset _ _

theorem label_fibers_partition {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι) :
    Finset.univ.biUnion (labelFiber Q label) = Q := by
  ext q
  constructor
  · intro hq
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hq
    exact labelFiber_subset Q label i hi
  · intro hq
    exact Finset.mem_biUnion.mpr ⟨label q,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hq,rfl⟩⟩

theorem label_fibers_disjoint {ι : Type*} (Q : Finset ℕ) (label : ℕ → ι) (i j : ι) (hij : i ≠ j) :
    Disjoint (labelFiber Q label i) (labelFiber Q label j) := by
  apply Finset.disjoint_left.mpr
  intro q hi hj
  exact hij ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

theorem sum_label_fibers {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι) (f : ℕ → ℝ) :
    (∑ i : ι,∑ q ∈ labelFiber Q label i,f q) = ∑ q ∈ Q,f q := by
  calc
    _ = ∑ q ∈ Finset.univ.biUnion (labelFiber Q label),f q :=
      (Finset.sum_biUnion (fun i _ j _ hij => label_fibers_disjoint Q label i j hij)).symm
    _ = _ := by rw [label_fibers_partition]

noncomputable def smallLabels {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι) (tau : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => ((labelFiber Q label i).card : ℝ) < tau)

noncomputable def discardedPoints {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι) (tau : ℝ) : Finset ℕ :=
  (smallLabels Q label tau).biUnion (labelFiber Q label)

theorem mem_discardedPoints {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι) (tau : ℝ) (q : ℕ) :
    q ∈ discardedPoints Q label tau ↔ q ∈ Q ∧ ((labelFiber Q label (label q)).card : ℝ) < tau := by
  constructor
  · intro hq
    obtain ⟨i,hi,hqi⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hqQ,he⟩ := Finset.mem_filter.mp hqi
    refine ⟨hqQ,?_⟩
    rw [he]
    exact (Finset.mem_filter.mp hi).2
  · rintro ⟨hq,hs⟩
    exact Finset.mem_biUnion.mpr ⟨label q,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩,
      Finset.mem_filter.mpr ⟨hq,rfl⟩⟩

theorem discardedPoints_subset {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι) (tau : ℝ) :
    discardedPoints Q label tau ⊆ Q := fun q hq => (mem_discardedPoints Q label tau q).mp hq |>.1

theorem sum_small_fibers {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι) (tau : ℝ) (f : ℕ → ℝ) :
    (∑ i ∈ smallLabels Q label tau,∑ q ∈ labelFiber Q label i,f q) = ∑ q ∈ discardedPoints Q label tau,f q :=
  (Finset.sum_biUnion (fun i _ j _ hij => label_fibers_disjoint Q label i j hij)).symm

theorem discardedPoints_card_bound {ι : Type*} [Fintype ι] (Q : Finset ℕ) (label : ℕ → ι)
    (tau : ℝ) (htau : 0 ≤ tau) :
    ((discardedPoints Q label tau).card : ℝ) ≤ (Fintype.card ι : ℝ)*tau := by
  calc
    _ ≤ ∑ i ∈ smallLabels Q label tau,((labelFiber Q label i).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ smallLabels Q label tau,tau := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2.le)
    _ = ((smallLabels Q label tau).card : ℝ)*tau := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ (smallLabels Q label tau)) htau

end ErdosInverseCells

end

section

namespace ErdosGeometricValueCells

noncomputable def coordinate (B xi q : ℝ) : ℝ := Real.log (B/q)/Real.log (1+xi)

noncomputable def valueIndex (B xi : ℝ) (k : ℕ) (q : ℝ) : Fin (k+1) :=
  ⟨min k ⌊coordinate B xi q⌋₊, Nat.lt_succ_of_le (min_le_left _ _)⟩

theorem coordinate_bounds {B xi q : ℝ} {k : ℕ} (hB : 0 < B) (hxi : 0 < xi)
    (hlo : B/(1+xi)^k ≤ q) (hhi : q ≤ B) :
    0 < q ∧ 0 ≤ coordinate B xi q ∧ coordinate B xi q ≤ k := by
  have hF : 0 < 1+xi := by linarith
  have hpow : 0 < (1+xi)^k := pow_pos hF _
  have hq : 0 < q := (div_pos hB hpow).trans_le hlo
  have hL : 0 < Real.log (1+xi) := Real.log_pos (by linarith)
  have hrat : 1 ≤ B/q := (one_le_div hq).mpr hhi
  have hratUpper : B/q ≤ (1+xi)^k := by
    apply (div_le_iff₀ hq).mpr
    have h := (div_le_iff₀ hpow).mp hlo
    simpa only [mul_comm] using h
  refine ⟨hq, div_nonneg (Real.log_nonneg hrat) hL.le, ?_⟩
  have hlog := Real.log_le_log (div_pos hB hq) hratUpper
  rw [Real.log_pow] at hlog
  exact (div_le_iff₀ hL).mpr hlog

theorem valueIndex_eq_floor {B xi q : ℝ} {k : ℕ} (hB : 0 < B) (hxi : 0 < xi)
    (hlo : B/(1+xi)^k ≤ q) (hhi : q ≤ B) :
    (valueIndex B xi k q).val = ⌊coordinate B xi q⌋₊ := by
  have hs := coordinate_bounds hB hxi hlo hhi
  have hfloor : ⌊coordinate B xi q⌋₊ ≤ k := by
    exact_mod_cast (Nat.floor_le hs.2.1).trans hs.2.2
  exact min_eq_right hfloor

theorem valueIndex_interval {B xi q : ℝ} {k : ℕ} (hB : 0 < B) (hxi : 0 < xi)
    (hlo : B/(1+xi)^k ≤ q) (hhi : q ≤ B) :
    B/(1+xi)^((valueIndex B xi k q).val+1) < q ∧
      q ≤ B/(1+xi)^(valueIndex B xi k q).val := by
  have hs := coordinate_bounds hB hxi hlo hhi
  have hF : 0 < 1+xi := by linarith
  have hL : 0 < Real.log (1+xi) := Real.log_pos (by linarith)
  have hfloor := valueIndex_eq_floor hB hxi hlo hhi
  have hl : ((valueIndex B xi k q).val : ℝ) ≤ coordinate B xi q := by
    rw [hfloor]
    exact Nat.floor_le hs.2.1
  have hu : coordinate B xi q < ((valueIndex B xi k q).val : ℝ)+1 := by
    rw [hfloor]
    exact Nat.lt_floor_add_one _
  have hlogLower := (le_div_iff₀ hL).mp hl
  have hlogUpper := (div_lt_iff₀ hL).mp hu
  have hpLower := Real.exp_le_exp.mpr hlogLower
  rw [Real.exp_nat_mul, Real.exp_log hF, Real.exp_log (div_pos hB hs.1)] at hpLower
  have hpUpper := Real.exp_lt_exp.mpr hlogUpper
  have he : (((valueIndex B xi k q).val : ℝ)+1)*Real.log (1+xi) =
      (((valueIndex B xi k q).val+1 : ℕ) : ℝ)*Real.log (1+xi) := by norm_num
  rw [he, Real.exp_nat_mul, Real.exp_log hF, Real.exp_log (div_pos hB hs.1)] at hpUpper
  constructor
  · apply (div_lt_iff₀ (pow_pos hF _)).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hs.1).mp hpUpper
  · apply (le_div_iff₀ (pow_pos hF _)).mpr
    simpa only [mul_comm] using (le_div_iff₀ hs.1).mp hpLower

end ErdosGeometricValueCells

end

section

namespace ErdosInverseCells
attribute [local instance] Classical.decEq

theorem exists_dense_retained_fiber {ι : Type*} [Fintype ι]
    (Q : Finset ℕ) (label : ℕ → ι) (tau sigma : ℝ) (hsigma : 0 ≤ sigma)
    (w f : ℕ → ℝ) (hw : ∀ q ∈ Q,0 ≤ w q) (hf : ∀ q ∈ Q,f q ≤ w q)
    (hmass : sigma*(∑ q ∈ Q,w q) < ∑ q ∈ Q,f q)
    (hdiscard : (∑ q ∈ discardedPoints Q label tau,w q) ≤ (sigma/2)*(∑ q ∈ Q,w q)) :
    ∃ i : ι,tau ≤ ((labelFiber Q label i).card : ℝ) ∧
      (sigma/2)*(∑ q ∈ labelFiber Q label i,w q) < ∑ q ∈ labelFiber Q label i,f q := by
  classical
  by_contra hno
  push Not at hno
  have hcell : ∀ i : ι,(∑ q ∈ labelFiber Q label i,f q) ≤
      (sigma/2)*(∑ q ∈ labelFiber Q label i,w q)+
        (if ((labelFiber Q label i).card : ℝ) < tau then ∑ q ∈ labelFiber Q label i,w q else 0) := by
    intro i
    have hWi : 0 ≤ ∑ q ∈ labelFiber Q label i,w q :=
      Finset.sum_nonneg (fun q hq => hw q (labelFiber_subset Q label i hq))
    by_cases hi : ((labelFiber Q label i).card : ℝ) < tau
    · rw [ite_eq_left hi]
      have hfi := Finset.sum_le_sum (fun q hq => hf q (labelFiber_subset Q label i hq))
      have hprod := mul_nonneg (show 0 ≤ sigma/2 by positivity) hWi
      linarith
    · rw [ite_eq_right hi,add_zero]
      exact hno i (le_of_not_gt hi)
  have hsmall : (∑ i : ι,if ((labelFiber Q label i).card : ℝ) < tau then ∑ q ∈ labelFiber Q label i,w q else 0) =
      ∑ q ∈ discardedPoints Q label tau,w q := by
    calc
      _ = ∑ i ∈ smallLabels Q label tau,∑ q ∈ labelFiber Q label i,w q := by
        simp only [smallLabels,Finset.sum_filter]
      _ = _ := sum_small_fibers Q label tau w
  have hall : (∑ q ∈ Q,f q) ≤ (sigma/2)*(∑ q ∈ Q,w q)+∑ q ∈ discardedPoints Q label tau,w q := by
    calc
      _ = ∑ i : ι,∑ q ∈ labelFiber Q label i,f q := (sum_label_fibers Q label f).symm
      _ ≤ ∑ i : ι,((sigma/2)*(∑ q ∈ labelFiber Q label i,w q)+
          (if ((labelFiber Q label i).card : ℝ) < tau then ∑ q ∈ labelFiber Q label i,w q else 0)) :=
        Finset.sum_le_sum (fun i _ => hcell i)
      _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,sum_label_fibers,hsmall]
  linarith

end ErdosInverseCells

end

section

namespace ErdosGeometricValueCells
attribute [local instance] Classical.decEq

theorem same_index_ratio {B xi q r : ℝ} {k : ℕ} (hB : 0 < B) (hxi : 0 < xi)
    (hq0 : B/(1+xi)^k ≤ q) (hq1 : q ≤ B)
    (hr0 : B/(1+xi)^k ≤ r) (hr1 : r ≤ B)
    (he : valueIndex B xi k q = valueIndex B xi k r) : q/r ≤ 1+xi := by
  have hq := valueIndex_interval hB hxi hq0 hq1
  have hr := valueIndex_interval hB hxi hr0 hr1
  have hrp := (coordinate_bounds hB hxi hr0 hr1).1
  have hF : 0 < 1+xi := by linarith
  rw [he] at hq
  have hscale : B/(1+xi)^(valueIndex B xi k r).val =
      (1+xi)*(B/(1+xi)^((valueIndex B xi k r).val+1)) := by
    calc
      _ = (B/(1+xi)^(valueIndex B xi k r).val)*((1+xi)/(1+xi)) := by
        rw [div_self hF.ne', mul_one]
      _ = _ := by
        rw [pow_succ]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  have hh := mul_lt_mul_of_pos_left hr.1 hF
  rw [← hscale] at hh
  exact (div_le_iff₀ hrp).mpr (hq.2.trans hh.le)

noncomputable def valueCell (Q : Finset ℕ) (B xi : ℝ) (k : ℕ) (i : Fin (k+1)) : Finset ℕ :=
  Q.filter (fun q => valueIndex B xi k q = i)

theorem valueCells_partition (Q : Finset ℕ) (B xi : ℝ) (k : ℕ) :
    Finset.univ.biUnion (valueCell Q B xi k) = Q := by
  ext q
  constructor
  · intro hq
    obtain ⟨i, _hi, hqi⟩ := Finset.mem_biUnion.mp hq
    exact (Finset.mem_filter.mp hqi).1
  · intro hq
    exact Finset.mem_biUnion.mpr ⟨valueIndex B xi k q, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hq, rfl⟩⟩

theorem valueCells_disjoint (Q : Finset ℕ) (B xi : ℝ) (k : ℕ) (i j : Fin (k+1)) (hij : i ≠ j) :
    Disjoint (valueCell Q B xi k i) (valueCell Q B xi k j) := by
  apply Finset.disjoint_left.mpr
  intro q hi hj
  exact hij ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

theorem sum_valueCells (Q : Finset ℕ) (B xi : ℝ) (k : ℕ) (F : ℕ → ℝ) :
    (∑ i : Fin (k+1), ∑ q ∈ valueCell Q B xi k i, F q) = ∑ q ∈ Q, F q := by
  calc
    _ = ∑ q ∈ Finset.univ.biUnion (valueCell Q B xi k), F q :=
      (Finset.sum_biUnion (fun i _ j _ hij => valueCells_disjoint Q B xi k i j hij)).symm
    _ = _ := by rw [valueCells_partition]

theorem valueCells_card_bound (Q : Finset ℕ) (B xi : ℝ) (k : ℕ) :
    (Q.image (fun q : ℕ => valueIndex B xi k q)).card ≤ k+1 := by
  simpa only [Fintype.card_fin] using Finset.card_le_univ (Q.image (fun q : ℕ => valueIndex B xi k q))

theorem same_cell_ratio (Q : Finset ℕ) (B xi : ℝ) (k : ℕ) (hB : 0 < B) (hxi : 0 < xi)
    (hQ : ∀ q ∈ Q, B/(1+xi)^k ≤ (q : ℝ) ∧ (q : ℝ) ≤ B)
    (i : Fin (k+1)) (q r : ℕ) (hq : q ∈ valueCell Q B xi k i)
    (hr : r ∈ valueCell Q B xi k i) : (q : ℝ)/(r : ℝ) ≤ 1+xi := by
  have hq' := Finset.mem_filter.mp hq
  have hr' := Finset.mem_filter.mp hr
  exact same_index_ratio hB hxi (hQ q hq'.1).1 (hQ q hq'.1).2
    (hQ r hr'.1).1 (hQ r hr'.1).2 (hq'.2.trans hr'.2.symm)

end ErdosGeometricValueCells

end

section

namespace ErdosInverseCells
open ErdosInverseHits ErdosGeometricValueCells
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def cofactorHit (q : ℕ) (a : ℕ → ℕ) : ℕ :=
  if hq : Squarefree q then primeHitRepresentative q hq a else 0

theorem cofactorHit_eq (q : ℕ) (hq : Squarefree q) (a : ℕ → ℕ) :
    cofactorHit q a = primeHitRepresentative q hq a := by simp only [cofactorHit,dite_eq_left hq]

theorem cofactorHit_spec (q : ℕ) (hq : Squarefree q) (a : ℕ → ℕ) :
    1 ≤ cofactorHit q a ∧ cofactorHit q a ≤ q ∧
      ∀ p ∈ q.primeFactors,cofactorHit q a%p = a p%p := by
  rw [cofactorHit_eq q hq a]
  have hh := primeHitRepresentative_spec q hq a
  exact ⟨hh.1,hh.2.1,(hh.2.2 _).mpr (Nat.ModEq.refl _)⟩

abbrev InitialLabel (k M0 : ℕ) := Fin (k+1) × ZMod M0 × ZMod M0

noncomputable def initialLabel (a : ℕ → ℕ) (B xi : ℝ) (k M0 q : ℕ) : InitialLabel k M0 :=
  ⟨valueIndex B xi k (q : ℝ),(q : ZMod M0),(cofactorHit q a : ZMod M0)⟩

noncomputable def initialCell (Q : Finset ℕ) (a : ℕ → ℕ) (B xi : ℝ) (k M0 : ℕ)
    (i : InitialLabel k M0) : Finset ℕ := labelFiber Q (initialLabel a B xi k M0) i

theorem initialLabel_card (k M0 : ℕ) [NeZero M0] :
    Fintype.card (InitialLabel k M0) = (k+1)*M0^2 := by
  simp only [InitialLabel,Fintype.card_prod,Fintype.card_fin,ZMod.card]
  ring

theorem same_initial_label (a : ℕ → ℕ) (B xi : ℝ) (k M0 q r : ℕ)
    (he : initialLabel a B xi k M0 q = initialLabel a B xi k M0 r) :
    valueIndex B xi k (q : ℝ) = valueIndex B xi k (r : ℝ) ∧
      Int.ModEq (M0 : ℤ) (q : ℤ) (r : ℤ) ∧
      Int.ModEq (M0 : ℤ) (cofactorHit q a : ℤ) (cofactorHit r a : ℤ) := by
  have hi := congrArg (fun i : InitialLabel k M0 => i.1) he
  have hq := congrArg (fun i : InitialLabel k M0 => i.2.1) he
  have hb := congrArg (fun i : InitialLabel k M0 => i.2.2) he
  exact ⟨hi,Int.natCast_modEq_iff.mpr ((ZMod.natCast_eq_natCast_iff q r M0).mp hq),
    Int.natCast_modEq_iff.mpr ((ZMod.natCast_eq_natCast_iff (cofactorHit q a) (cofactorHit r a) M0).mp hb)⟩

noncomputable def cellUpper (B xi : ℝ) {k M0 : ℕ} (i : InitialLabel k M0) : ℝ :=
  B/(1+xi)^i.1.val

theorem initial_cell_interval (Q : Finset ℕ) (a : ℕ → ℕ) (B xi : ℝ) (k M0 : ℕ)
    (hB : 0 < B) (hxi : 0 < xi)
    (hQ : ∀ q ∈ Q,B/(1+xi)^k ≤ (q : ℝ) ∧ (q : ℝ) ≤ B)
    (i : InitialLabel k M0) (q : ℕ) (hq : q ∈ initialCell Q a B xi k M0 i) :
    q ∈ Q ∧ 0 < (q : ℝ) ∧ (q : ℝ) ≤ cellUpper B xi i ∧ cellUpper B xi i ≤ (1+xi)*(q : ℝ) := by
  have hm := (mem_labelFiber Q (initialLabel a B xi k M0) i q).mp hq
  have hi : valueIndex B xi k (q : ℝ) = i.1 := congrArg (fun j : InitialLabel k M0 => j.1) hm.2
  have hinterval := valueIndex_interval hB hxi (hQ q hm.1).1 (hQ q hm.1).2
  rw [hi] at hinterval
  have hqpos : 0 < (q : ℝ) := (coordinate_bounds hB hxi (hQ q hm.1).1 (hQ q hm.1).2).1
  have hlow : cellUpper B xi i/(1+xi) < (q : ℝ) := by
    unfold cellUpper
    rw [div_div,← pow_succ]
    exact hinterval.1
  refine ⟨hm.1,hqpos,hinterval.2,?_⟩
  have hh := (div_lt_iff₀ (by linarith : 0 < 1+xi)).mp hlow
  nlinarith

end ErdosInverseCells

end

section

namespace ErdosInverseCells

theorem mem_initialCell (Q : Finset ℕ) (a : ℕ → ℕ) (B xi : ℝ) (k M0 : ℕ)
    (i : InitialLabel k M0) (q : ℕ) :
    q ∈ initialCell Q a B xi k M0 i ↔ q ∈ Q ∧ initialLabel a B xi k M0 q = i :=
  mem_labelFiber Q (initialLabel a B xi k M0) i q

theorem initial_cell_congruences (Q : Finset ℕ) (a : ℕ → ℕ) (B xi : ℝ) (k M0 : ℕ)
    (i : InitialLabel k M0) (q r : ℕ) (hq : q ∈ initialCell Q a B xi k M0 i)
    (hr : r ∈ initialCell Q a B xi k M0 i) :
    Int.ModEq (M0 : ℤ) (q : ℤ) (r : ℤ) ∧
      Int.ModEq (M0 : ℤ) (cofactorHit q a : ℤ) (cofactorHit r a : ℤ) := by
  have hq' := (mem_initialCell Q a B xi k M0 i q).mp hq
  have hr' := (mem_initialCell Q a B xi k M0 i r).mp hr
  exact (same_initial_label a B xi k M0 q r (hq'.2.trans hr'.2.symm)).2

theorem initial_cell_weight_spread (Q : Finset ℕ) (a : ℕ → ℕ) (B xi : ℝ) (k M0 : ℕ)
    (hB : 0 < B) (hxi : 0 < xi)
    (hQ : ∀ q ∈ Q,B/(1+xi)^k ≤ (q : ℝ) ∧ (q : ℝ) ≤ B)
    (i : InitialLabel k M0) (q r : ℕ) (hq : q ∈ initialCell Q a B xi k M0 i)
    (hr : r ∈ initialCell Q a B xi k M0 i) :
    (q : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹ := by
  have hq' := initial_cell_interval Q a B xi k M0 hB hxi hQ i q hq
  have hr' := initial_cell_interval Q a B xi k M0 hB hxi hQ i r hr
  have hratio : (r : ℝ) ≤ (1+xi)*(q : ℝ) := hr'.2.2.1.trans hq'.2.2.2
  have hh : (1 : ℝ)/(q : ℝ) ≤ (1+xi)/(r : ℝ) :=
    (div_le_div_iff₀ hq'.2.1 hr'.2.1).mpr (by simpa only [one_mul] using hratio)
  simpa only [one_div,div_eq_mul_inv,one_mul] using hh

end ErdosInverseCells

end

section

namespace ErdosInverseRefinement
open ErdosInverseCells

abbrev RefinementLabel (W : ℕ) := ZMod W × ZMod W

noncomputable def refinementLabel (a : ℕ → ℕ) (W q : ℕ) : RefinementLabel W :=
  ⟨(q : ZMod W),(cofactorHit q a : ZMod W)⟩

noncomputable def refinementCell (C : Finset ℕ) (a : ℕ → ℕ) (W : ℕ) (i : RefinementLabel W) : Finset ℕ :=
  labelFiber C (refinementLabel a W) i

theorem refinementLabel_card (W : ℕ) [NeZero W] : Fintype.card (RefinementLabel W) = W^2 := by
  simp only [RefinementLabel,Fintype.card_prod,ZMod.card]
  ring

theorem mem_refinementCell (C : Finset ℕ) (a : ℕ → ℕ) (W : ℕ) (i : RefinementLabel W) (q : ℕ) :
    q ∈ refinementCell C a W i ↔ q ∈ C ∧ refinementLabel a W q = i :=
  mem_labelFiber C (refinementLabel a W) i q

theorem refinement_congruences (C : Finset ℕ) (a : ℕ → ℕ) (W : ℕ) (i : RefinementLabel W) (q r : ℕ)
    (hq : q ∈ refinementCell C a W i) (hr : r ∈ refinementCell C a W i) :
    Int.ModEq (W : ℤ) (q : ℤ) (r : ℤ) ∧
      Int.ModEq (W : ℤ) (cofactorHit q a : ℤ) (cofactorHit r a : ℤ) := by
  have hq' := (mem_refinementCell C a W i q).mp hq
  have hr' := (mem_refinementCell C a W i r).mp hr
  have he := hq'.2.trans hr'.2.symm
  have h1 := congrArg (fun j : RefinementLabel W => j.1) he
  have h2 := congrArg (fun j : RefinementLabel W => j.2) he
  exact ⟨Int.natCast_modEq_iff.mpr ((ZMod.natCast_eq_natCast_iff q r W).mp h1),
    Int.natCast_modEq_iff.mpr ((ZMod.natCast_eq_natCast_iff (cofactorHit q a) (cofactorHit r a) W).mp h2)⟩

end ErdosInverseRefinement

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseCells
open ErdosCofactorChoices ErdosInverseBoxHeight ErdosInverseEuler

theorem source_initial_label_count (C eps : ℝ) (hC : 0 ≤ C) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,∀ k : ℕ,(k : ℝ) ≤ C*Real.log (sourceB z) →
      (((k+1)*(smallModulus (sourceW z))^2 : ℕ) : ℝ) ≤ (sourceZ z)^eps := by
  have hZ := (tendsto_rpow_atTop (by positivity : 0 < eps/2)).comp sourceZ_tendsto_atTop
  filter_upwards [source_log_budget,smallModulus_mul_log_power 2 1 (eps/2) (by positivity),
    hZ.eventually_ge_atTop (C+1),Real.tendsto_log_atTop.eventually_ge_atTop 1] with z hs hm hcoef hL1
  intro k hk
  have hkL : (k : ℝ) ≤ C*Real.log z := by
    have hh := hk.trans (mul_le_mul_of_nonneg_left hs.2.2.2.2 hC)
    have hlog := Real.log_le_sub_one_of_pos hs.1
    have hL : Real.log (Real.log z) ≤ Real.log z := by linarith
    exact hh.trans (mul_le_mul_of_nonneg_left hL hC)
  have hk1 : (k : ℝ)+1 ≤ (C+1)*Real.log z := by nlinarith
  have hM : (smallModulus (sourceW z) : ℝ)^2*Real.log z ≤ (sourceZ z)^(eps/2) := by
    simpa only [pow_one] using hm
  have hZpos : 0 < sourceZ z := Real.exp_pos _
  calc
    _ = ((k : ℝ)+1)*(smallModulus (sourceW z) : ℝ)^2 := by push_cast;rfl
    _ ≤ ((C+1)*Real.log z)*(smallModulus (sourceW z) : ℝ)^2 :=
      mul_le_mul_of_nonneg_right hk1 (sq_nonneg _)
    _ = (C+1)*((smallModulus (sourceW z) : ℝ)^2*Real.log z) := by ring
    _ ≤ (sourceZ z)^(eps/2)*(sourceZ z)^(eps/2) :=
      mul_le_mul hcoef hM (by positivity) (Real.rpow_nonneg hZpos.le _)
    _ = (sourceZ z)^eps := by
      rw [← Real.rpow_add hZpos]
      congr 1
      ring

end ErdosInverseCells

end

end Erdos970

end OAI
