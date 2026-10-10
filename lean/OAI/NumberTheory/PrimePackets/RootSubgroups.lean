import Mathlib
import OAI.NumberTheory.PrimePackets.AtomMass
import OAI.NumberTheory.PrimePackets.EntropyMixtures

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
namespace PrimeDegreePackets

 
lemma diag2n_decompose {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    {i j : ι} (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n hij a ha =
      Matrix.SpecialLinearGroup.transvection hij a *
      Matrix.SpecialLinearGroup.transvection hij.symm (-a⁻¹) *
      Matrix.SpecialLinearGroup.transvection hij a *
      Matrix.SpecialLinearGroup.transvection hij (-1) *
      Matrix.SpecialLinearGroup.transvection hij.symm 1 *
      Matrix.SpecialLinearGroup.transvection hij (-1) := by
  ext r c
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.diag2n_coe,
    Matrix.SpecialLinearGroup.transvection_coe,mul_add,add_mul,Matrix.one_mul,Matrix.mul_one]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hci : c = i <;> by_cases hcj : c = j
  all_goals simp_all [Matrix.single_apply,Matrix.diagonal_apply,
    Matrix.one_apply,eq_comm]

 
theorem specialLinear_transvection_induction {ι F : Type*} [Fintype ι]
    [DecidableEq ι] [Nontrivial ι] [Field F]
    (P : Matrix.SpecialLinearGroup ι F → Prop)
    (hroot : ∀ (i j : ι) (hij : i ≠ j) (a : F),
      P (Matrix.SpecialLinearGroup.transvection hij a))
    (hmul : ∀ A B, P A → P B → P (A*B))
    (g : Matrix.SpecialLinearGroup ι F) : P g := by
  apply Matrix.SpecialLinearGroup.diagonal_transvection_induction' P g _ hroot hmul
  intro i j hij a ha
  rw [diag2n_decompose hij a ha]
  refine hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ ?_ ?_) ?_) ?_) ?_) ?_
  all_goals exact hroot _ _ _ _

end PrimeDegreePackets


namespace PrimeDegreePackets

 
lemma transvection_chain_commutator {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : F) :
    Matrix.SpecialLinearGroup.transvection hij a *
      Matrix.SpecialLinearGroup.transvection hjk b *
      Matrix.SpecialLinearGroup.transvection hij (-a) *
      Matrix.SpecialLinearGroup.transvection hjk (-b) =
      Matrix.SpecialLinearGroup.transvection hik (a*b) := by
  ext r c
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.transvection_coe,
    mul_add,add_mul,Matrix.one_mul,Matrix.mul_one]
  by_cases hri : r = i <;> by_cases hrj : r = j <;> by_cases hrk : r = k <;>
    by_cases hci : c = i <;> by_cases hcj : c = j <;> by_cases hck : c = k
  all_goals simp_all [Matrix.single_apply,Matrix.one_apply,eq_comm]

 
lemma root_subgroup_chain {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (H : Subgroup (Matrix.SpecialLinearGroup ι F)) {i j k : ι}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hijH : ∀ a : F, Matrix.SpecialLinearGroup.transvection hij a ∈ H)
    (hjkH : ∀ b : F, Matrix.SpecialLinearGroup.transvection hjk b ∈ H) :
    ∀ c : F, Matrix.SpecialLinearGroup.transvection hik c ∈ H := by
  intro c
  rw [← mul_one c,← transvection_chain_commutator hij hjk hik c 1]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hijH _) (hjkH _)) (hijH _)) (hjkH _)

end PrimeDegreePackets


namespace PrimeDegreePackets

 
def invariantRightSubgroup {n : ℕ} (μ : Measure (X n)) : Subgroup (G n) where
  carrier := {g | Measure.map (fun x => rightAction x g) μ = μ}
  one_mem' := by
    change Measure.map (fun x : X n => rightAction x 1) μ = μ
    rw [show (fun x : X n => rightAction x 1) = id from funext rightAction_one]
    exact Measure.map_id
  mul_mem' {g h} hg hh := by
    change Measure.map (fun x => rightAction x (g*h)) μ = μ
    have heq : (fun x : X n => rightAction x (g*h)) =
        ((fun x => rightAction x h) ∘ (fun x => rightAction x g)) := by
      funext x
      exact (rightAction_mul x g h).symm
    rw [heq,←Measure.map_map (continuous_rightAction h).measurable
      (continuous_rightAction g).measurable,hg,hh]
  inv_mem' {g} hg := by
    change Measure.map (fun x => rightAction x g⁻¹) μ = μ
    calc
      _ = Measure.map (fun x => rightAction x g⁻¹)
        (Measure.map (fun x => rightAction x g) μ) := by rw [hg]
      _ = μ := by
        rw [Measure.map_map (continuous_rightAction g⁻¹).measurable
          (continuous_rightAction g).measurable]
        have heq : (fun x : X n => rightAction (rightAction x g) g⁻¹) = id := by
          funext x
          simp
        rw [show ((fun x : X n => rightAction x g⁻¹) ∘
          (fun x => rightAction x g)) = id from heq,Measure.map_id]

 

theorem right_invariant_of_all_roots {n : ℕ} (hn : 2 ≤ n)
    (μ : Measure (X n))
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j) (a : ℝ),
      Measure.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) μ = μ) :
    ∀ g : G n, Measure.map (fun x => rightAction x g) μ = μ := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  intro g
  exact specialLinear_transvection_induction (fun g => g ∈ invariantRightSubgroup μ)
    hroot (fun _ _ hg hh => (invariantRightSubgroup μ).mul_mem hg hh) g

end PrimeDegreePackets

open scoped Topology Classical Matrix
namespace PrimeDegreePackets

lemma diagonal_conjugation_transvection {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) {i j : Fin n} (hij : i ≠ j) (a t : ℝ) :
    diagonalOneParameter ell hell t * Matrix.SpecialLinearGroup.transvection hij a *
      diagonalOneParameter ell hell (-t) =
      Matrix.SpecialLinearGroup.transvection hij (Real.exp ((ell i-ell j)*t)*a) := by
  ext r s
  rw [conjugation_entry]
  simp only [Matrix.SpecialLinearGroup.transvection_coe,Matrix.add_apply]
  by_cases hrs : r = s <;> by_cases hri : r = i <;> by_cases hsj : s = j
  all_goals simp_all [Matrix.single_apply,Matrix.one_apply,eq_comm]

lemma root_mem_positive_reparameterize {d : ℕ} (H : Subgroup (G (d+1)))
    (hA : ∀ u : LogCoordinates d, diagonalFlow u ∈ H)
    {i j : Fin (d+1)} (hij : i ≠ j) {a : ℝ} (ha : 0 < a)
    (hu : Matrix.SpecialLinearGroup.transvection hij a ∈ H)
    {b : ℝ} (hb : 0 < b) : Matrix.SpecialLinearGroup.transvection hij b ∈ H := by
  let ell := regularDiagonalWeights d
  have he : ell i-ell j ≠ 0 := by
    have hh := regularDiagonalWeights_separated d i j hij
    intro he
    change 1 ≤ |ell i-ell j| at hh
    rw [he,abs_zero] at hh
    linarith
  let t := Real.log (b/a) / (ell i-ell j)
  have ht : (ell i-ell j)*t = Real.log (b/a) := by
    dsimp [t]
    field_simp
  have hp : Real.exp ((ell i-ell j)*t)*a = b := by
    rw [ht,Real.exp_log (div_pos hb ha),div_mul_cancel₀ _ ha.ne']
  have hD (s : ℝ) : diagonalOneParameter ell (regularDiagonalWeights_sum d) s ∈ H := by
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hu' := H.mul_mem (H.mul_mem (hD t) hu) (hD (-t))
  rw [diagonal_conjugation_transvection, hp] at hu'
  exact hu'

 

lemma root_mem_of_nonzero_parameter {d : ℕ} (H : Subgroup (G (d+1)))
    (hA : ∀ u : LogCoordinates d, diagonalFlow u ∈ H)
    {i j : Fin (d+1)} (hij : i ≠ j) {a : ℝ} (ha : a ≠ 0)
    (hu : Matrix.SpecialLinearGroup.transvection hij a ∈ H) :
    ∀ b : ℝ, Matrix.SpecialLinearGroup.transvection hij b ∈ H := by
  have habs : Matrix.SpecialLinearGroup.transvection hij |a| ∈ H := by
    rcases le_total 0 a with h | h
    · simpa only [abs_of_nonneg h] using hu
    · simpa only [Matrix.SpecialLinearGroup.transvection_inv,abs_of_nonpos h] using H.inv_mem hu
  have hpos {b : ℝ} (hb : 0 < b) : Matrix.SpecialLinearGroup.transvection hij b ∈ H :=
    root_mem_positive_reparameterize H hA hij (abs_pos.mpr ha) habs hb
  intro b
  rcases lt_trichotomy 0 b with hb | hb | hb
  · exact hpos hb
  · subst b
    have hz : Matrix.SpecialLinearGroup.transvection hij (0:ℝ) = 1 := by
      ext r c
      simp
    rw [hz]
    exact H.one_mem
  · simpa only [Matrix.SpecialLinearGroup.transvection_inv,neg_neg] using
      H.inv_mem (hpos (neg_pos.mpr hb))

 
def rootInvarianceRelation {n : ℕ} (μ : Measure (X n)) (i j : Fin n) : Prop :=
  i = j ∨ ∃ hij : i ≠ j, ∀ a : ℝ,
    Matrix.SpecialLinearGroup.transvection hij a ∈ invariantRightSubgroup μ

lemma rootInvarianceRelation_trans {n : ℕ} (μ : Measure (X n)) :
    ∀ ⦃i j k : Fin n⦄, rootInvarianceRelation μ i j →
      rootInvarianceRelation μ j k → rootInvarianceRelation μ i k := by
  intro i j k hij hjk
  rcases hij with rfl | ⟨hij,Hij⟩
  · exact hjk
  rcases hjk with rfl | ⟨hjk,Hjk⟩
  · exact Or.inr ⟨hij,Hij⟩
  by_cases hik : i = k
  · exact Or.inl hik
  exact Or.inr ⟨hik,root_subgroup_chain _ hij hjk hik Hij Hjk⟩

 

theorem right_invariant_of_nontrivial_roots {d : ℕ} (hd : 1 ≤ d)
    (μ : Measure (X (d+1)))
    (hA : ∀ u : LogCoordinates d, Measure.map (fun x => rightAction x (diagonalFlow u)) μ = μ)
    (hroot : ∀ (i j : Fin (d+1)) (hij : i ≠ j), ∃ a : ℝ, a ≠ 0 ∧
      Measure.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) μ = μ) :
    ∀ g : G (d+1), Measure.map (fun x => rightAction x g) μ = μ := by
  apply right_invariant_of_all_roots (by omega) μ
  intro i j hij a
  obtain ⟨b,hb,hbu⟩ := hroot i j hij
  exact root_mem_of_nonzero_parameter (invariantRightSubgroup μ) hA hij hb hbu a

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma observationEntropy_le_joint {Y α β : Type*} [MeasurableSpace Y]
    [Fintype α] [Fintype β] (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a}) (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    observationEntropy μ P ≤ observationEntropy μ (fun y => (P y,Q y)) := by
  unfold observationEntropy finiteShannon
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro a _
  dsimp only
  rw [← observation_joint_row μ P Q hP hQ a]
  exact negMulLog_sum_le _ (fun _ => measureReal_nonneg)

lemma observationEntropy_joint_eq_of_refines {Y α β : Type*} [MeasurableSpace Y]
    [Fintype α] [Fintype β] (μ : Measure Y) (P : Y → α) (Q : Y → β)
    (h : ∀ x y, Q x = Q y → P x = P y) :
    observationEntropy μ (fun y => (P y,Q y)) = observationEntropy μ Q := by
  unfold observationEntropy finiteShannon
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  dsimp only
  by_cases hb : ∃ x, Q x = b
  · obtain ⟨x,hx⟩ := hb
    have he (a : α) : {y | (P y,Q y) = (a,b)} =
        if a = P x then {y | Q y = b} else ∅ := by
      split_ifs with ha
      · subst a
        ext y
        simp only [mem_ofPred_eq,Prod.mk.injEq]
        exact ⟨And.right,fun hy => ⟨h y x (hy.trans hx.symm),hy⟩⟩
      · ext y
        simp only [mem_ofPred_eq,Prod.mk.injEq,mem_empty_iff_false,iff_false,not_and]
        intro hya hyb
        exact ha (hya.symm.trans (h y x (hyb.trans hx.symm)))
    simp only [he]
    simp only [apply_ite,measureReal_empty,Real.negMulLog_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  · have hQb : {y | Q y = b} = ∅ := by
      ext y
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
      exact fun hy => hb ⟨y,hy⟩
    have he (a : α) : {y | (P y,Q y) = (a,b)} = ∅ := by
      ext y
      simp only [mem_ofPred_eq,Prod.mk.injEq,mem_empty_iff_false,iff_false,not_and]
      exact fun _ hy => hb ⟨y,hy⟩
    simp only [he,hQb,measureReal_empty,Real.negMulLog_zero,Finset.sum_const_zero]

lemma observationEntropy_le_of_refines {Y α β : Type*} [MeasurableSpace Y]
    [Fintype α] [Fintype β] (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a}) (hQ : ∀ b, MeasurableSet {y | Q y = b})
    (h : ∀ x y, Q x = Q y → P x = P y) :
    observationEntropy μ P ≤ observationEntropy μ Q := by
  exact (observationEntropy_le_joint μ P Q hP hQ).trans_eq
    (observationEntropy_joint_eq_of_refines μ P Q h)

lemma orbitEntropy_one {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (T : Y → Y) (P : Y → α) :
    observationEntropy μ (orbitName T P 1) = observationEntropy μ P := by
  have heq : orbitName T P 1 = fun y => (Equiv.funUnique (Fin 1) α).symm (P y) := by
    ext y i
    simp [orbitName]
  rw [heq,observationEntropy_equiv]

lemma orbitEntropy_le_mul {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) :
    observationEntropy μ (orbitName T P N) ≤ N*observationEntropy μ P := by
  induction N with
  | zero =>
    have hzero : {y | orbitName T P 0 y = (default : Fin 0 → α)} = Set.univ := by
      ext y
      simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true]
      exact Subsingleton.elim _ _
    simp [observationEntropy,finiteShannon,hzero,Measure.real]
  | succ N ih =>
    have H := orbitEntropy_subadditive μ hT P hP N 1
    dsimp only at H
    rw [orbitEntropy_one] at H
    push_cast
    nlinarith

 

lemma entropyRate_le_coding_error {Y α β γ : Type*} [MeasurableSpace Y]
    [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (Q : Y → β) (E : Y → γ)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b})
    (hE : ∀ c, MeasurableSet {y | E y = c})
    (hcode : ∀ N x y, Q x = Q y → orbitName T E N x = orbitName T E N y →
      orbitName T P N x = orbitName T P N y) :
    observationEntropyRate μ T P ≤ observationEntropy μ E := by
  have H (N : ℕ) : observationEntropy μ (orbitName T P N) ≤
      observationEntropy μ Q + N*observationEntropy μ E := by
    let R : Y → β × (Fin N → γ) := fun y => (Q y,orbitName T E N y)
    have hR z : MeasurableSet {y | R y = z} := by
      simpa only [R,Prod.eq_iff_fst_eq_snd_eq,Set.ofPred_and] using
        (hQ z.1).inter (orbitName_measurable_fiber hT.measurable hE N z.2)
    have H₁ := observationEntropy_le_of_refines μ (orbitName T P N) R
      (orbitName_measurable_fiber hT.measurable hP N) hR
      (fun x y h => hcode N x y (congrArg Prod.fst h) (congrArg Prod.snd h))
    exact H₁.trans ((observationEntropy_joint_le μ Q (orbitName T E N) hQ
      (orbitName_measurable_fiber hT.measurable hE N)).trans
      (add_le_add le_rfl (orbitEntropy_le_mul μ hT E hE N)))
  have HC : Tendsto (fun N : ℕ => observationEntropy μ Q / (N:ℝ) + observationEntropy μ E)
      atTop (𝓝 (observationEntropy μ E)) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add_const
      (observationEntropy μ E)
  apply le_of_tendsto_of_tendsto (tendsto_observationEntropyRate μ hT P hP) HC
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have HN := (div_le_div_of_nonneg_right (H N) hn.le)
  simpa only [add_div,mul_div_cancel_left₀ _ hn.ne'] using HN

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma observationEntropy_small_of_almost_constant {Y α : Type*}
    [MeasurableSpace Y] [Fintype α] (a₀ : α) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α),
      (∀ a, MeasurableSet {y | P y = a}) →
      μ.real {y | P y ≠ a₀} < δ → observationEntropy μ P < ε := by
  let p₀ : α → ℝ := fun a => if a = a₀ then 1 else 0
  have hp₀ : finiteShannon p₀ = 0 := by simp [finiteShannon,p₀,apply_ite]
  have hcont : ContinuousAt (finiteShannon (α := α)) p₀ := continuous_finiteShannon.continuousAt
  obtain ⟨δ,hδ,Hδ⟩ := Metric.continuousAt_iff.mp hcont ε hε
  refine ⟨δ/2,by positivity,?_⟩
  intro μ _ P hP hbad
  let p : α → ℝ := fun a => μ.real {y | P y = a}
  have hc : μ.real {y | P y = a₀} + μ.real {y | P y ≠ a₀} = 1 := by
    have H := measureReal_add_measureReal_compl (hP a₀) (μ := μ)
    have he : {y | P y ≠ a₀} = {y | P y = a₀}ᶜ := by ext y; simp
    rw [he]
    simpa using H
  have hd : dist p p₀ < δ := by
    apply lt_of_le_of_lt ((dist_pi_le_iff (show 0 ≤ δ/2 by positivity)).mpr ?_) (by linarith)
    intro a
    rw [Real.dist_eq]
    by_cases ha : a = a₀
    · subst a
      simp only [p,p₀,ite_eq_left rfl]
      rw [abs_of_nonpos (by have := measureReal_le_one (μ := μ) (s := {y | P y = a₀}); linarith)]
      linarith
    · simp only [p,p₀,ite_eq_right ha,sub_zero,abs_of_nonneg measureReal_nonneg]
      exact (measureReal_mono (show {y | P y = a} ⊆ {y | P y ≠ a₀} from
        fun y hy h => ha (hy.symm.trans h))).trans hbad.le
  have H := Hδ hd
  rw [hp₀,Real.dist_eq,sub_zero] at H
  exact (le_abs_self _).trans_lt H

 

lemma finite_compact_cores_separated {Y α : Type*} [MetricSpace Y] [Fintype α]
    (K : α → Set Y) (hK : ∀ a, IsCompact (K a))
    (hpair : Pairwise (fun a b => Disjoint (K a) (K b))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b, a ≠ b → ∀ x ∈ K a, ∀ y ∈ K b, δ < dist x y := by
  have H (i : α × α) : ∃ r : ℝ, 0 < r ∧
      (i.1 ≠ i.2 → ∀ x ∈ K i.1, ∀ y ∈ K i.2, r < dist x y) := by
    by_cases hi : i.1 = i.2
    · exact ⟨1,by norm_num,fun h => (h hi).elim⟩
    obtain ⟨r,hr,Hr⟩ := Metric.exists_pos_forall_lt_edist (hK i.1) (hK i.2).isClosed (hpair hi)
    refine ⟨r,hr,fun _ x hx y hy => ?_⟩
    have := Hr x hx y hy
    rw [edist_nndist] at this
    exact_mod_cast this
  choose r hr Hr using H
  have Hmin (s : Finset (α × α)) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ r i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨δ,hδ,Hδ⟩ := ih
      refine ⟨min δ (r i),lt_min hδ (hr i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (Hδ j hj)
  obtain ⟨δ,hδ,Hδ⟩ := Hmin Finset.univ
  exact ⟨δ,hδ,fun a b hab x hx y hy => (Hδ (a,b) (Finset.mem_univ _)).trans_lt
    (Hr (a,b) hab x hx y hy)⟩

 

lemma observationEntropyRate_eq_zero_of_isometry {Y α : Type*}
    [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (hiso : Isometry T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    observationEntropyRate μ T P = 0 := by
  apply le_antisymm _ (observationEntropyRate_nonneg μ hT.measurable P hP)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ,hδ,Hδ⟩ := observationEntropy_small_of_almost_constant (Y := Y) (none : Option α) hε
  let η : ℝ := δ / ((Fintype.card α : ℝ)+1)
  have hη : 0 < η := div_pos hδ (by positivity)
  have HK (a : α) : ∃ K : Set Y, K ⊆ {y | P y = a} ∧ IsCompact K ∧
      μ.real ({y | P y = a} \ K) < η := by
    obtain ⟨K,hsub,hcomp,hsmall⟩ := (hP a).exists_isCompact_sdiff_lt
      (measure_ne_top μ _) (ENNReal.ofReal_ne_zero_iff.mpr hη)
    refine ⟨K,hsub,hcomp,?_⟩
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hsmall |>.trans_eq
      (ENNReal.toReal_ofReal hη.le)
  choose K hsub hK hsmall using HK
  have hpair : Pairwise (fun a b => Disjoint (K a) (K b)) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro x hx hy
    exact hab ((hsub a hx).symm.trans (hsub b hy))
  obtain ⟨r,hr,Hr⟩ := finite_compact_cores_separated K hK hpair
  obtain ⟨k,Q,hQ,HQ⟩ := finite_measurable_small_fibers (id : Y → Y)
    measurable_id isCompact_univ (fun _ => Set.mem_univ _) hr
  let E : Y → Option α := fun y => if y ∈ K (P y) then none else some (P y)
  have hEnone : {y | E y = none} = ⋃ a, K a := by
    ext y
    simp only [E,mem_ofPred_eq,mem_iUnion]
    constructor
    · intro h
      by_cases hy : y ∈ K (P y)
      · exact ⟨P y,hy⟩
      · simp [hy] at h
    · rintro ⟨a,ha⟩
      have he : P y = a := hsub a ha
      simp [he,ha]
  have hEsome (a : α) : {y | E y = some a} = {y | P y = a} \ K a := by
    ext y
    by_cases hy : y ∈ K (P y)
    · have hn : ¬ (P y = a ∧ y ∉ K a) := by
        rintro ⟨he,hn⟩
        exact hn (by simpa only [he] using hy)
      simp [E,hy,hn]
    · simp only [E,ite_eq_right hy,Option.some.injEq,mem_ofPred_eq,Set.mem_sdiff]
      constructor
      · intro he
        exact ⟨he,by simpa only [he] using hy⟩
      · exact And.left
  have hE : ∀ a, MeasurableSet {y | E y = a} := by
    intro a
    cases a with
    | none => rw [hEnone]; exact MeasurableSet.iUnion (fun a => (hK a).measurableSet)
    | some a => rw [hEsome]; exact (hP a).diff (hK a).measurableSet
  have hEbad : {y | E y ≠ none} = ⋃ a, ({y | P y = a} \ K a) := by
    ext y
    simp only [mem_ofPred_eq,mem_iUnion,Set.mem_sdiff]
    by_cases hy : y ∈ K (P y)
    · simp only [E,ite_eq_left hy,ne_eq,not_true_eq_false,false_iff,not_exists,not_and,not_not]
      intro a he
      simpa only [← he] using hy
    · simp only [E,ite_eq_right hy,ne_eq,Option.some_ne_none,not_false_eq_true,true_iff]
      exact ⟨P y,rfl,hy⟩
  have hmass : μ.real {y | E y ≠ none} < δ := by
    rw [hEbad]
    calc
      μ.real (⋃ a, {y | P y = a} \ K a) ≤ ∑ a, μ.real ({y | P y = a} \ K a) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _a : α, η := Finset.sum_le_sum (fun a _ => (hsmall a).le)
      _ = (Fintype.card α : ℝ)*η := by simp
      _ < δ := by
        dsimp [η]
        rw [← mul_div_assoc,div_lt_iff₀ (by positivity)]
        nlinarith
  have hcode N x y (hxy : Q x = Q y)
      (hname : orbitName T E N x = orbitName T E N y) :
      orbitName T P N x = orbitName T P N y := by
    ext j
    change P (T^[j.val] x) = P (T^[j.val] y)
    have hdist (n : ℕ) : dist (T^[n] x) (T^[n] y) = dist x y := by
      induction n with
      | zero => rfl
      | succ n ih => simpa only [Function.iterate_succ_apply',hiso.dist_eq] using ih
    have hd : dist (T^[j.val] x) (T^[j.val] y) < r := by
      simpa only [hdist,id_eq] using HQ x y hxy
    have he := congrFun hname j
    change E (T^[j.val] x) = E (T^[j.val] y) at he
    by_cases hx : T^[j.val] x ∈ K (P (T^[j.val] x))
    · by_cases hy : T^[j.val] y ∈ K (P (T^[j.val] y))
      · by_contra hne
        exact (not_lt_of_gt (Hr _ _ hne _ hx _ hy)) hd
      · simp [E,hx,hy] at he
    · by_cases hy : T^[j.val] y ∈ K (P (T^[j.val] y))
      · simp [E,hx,hy] at he
      · simpa [E,hx,hy] using he
  have H := entropyRate_le_coding_error μ hT P Q E hP hQ hE hcode
  simpa only [zero_add] using H.trans (Hδ μ E hE hmass).le

lemma measureEntropy_eq_zero_of_isometry {Y : Type*}
    [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (hiso : Isometry T) :
    measureEntropy μ T = 0 := by
  unfold measureEntropy
  apply le_antisymm _ bot_le
  refine iSup_le fun k => iSup_le fun P => iSup_le fun hP => ?_
  rw [observationEntropyRate_eq_zero_of_isometry μ hT hiso P hP, ENNReal.ofReal_zero]
  exact le_rfl

end PrimeDegreePackets
end
end

end OAI
