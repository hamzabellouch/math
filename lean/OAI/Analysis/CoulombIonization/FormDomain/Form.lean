import Mathlib
import OAI.Analysis.CoulombIonization.Variational.InsertionSwap

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

def FormZeroAt {N : ℕ} (ψ : FormVector N) (x : Configuration N) : Prop :=
  ∀ s, ψ.value s x = 0 ∧ ∀ i a, ψ.gradient s i a x = 0

lemma insertionTerm_zero {N : ℕ} {T : FormVector (N+1)} {x : Configuration (N+1)}
    (i : Fin (N+1)) (hx : FormZeroAt T (x ∘ insertionSwap i)) :
    FormZeroAt (insertionTerm T i) x := by
  intro s
  constructor
  · rw [insertionTerm_value,(hx _).1,mul_zero]
  · intro j a
    change _ * T.gradient (s ∘ (insertionSwap i).symm) (insertionSwap i j) a
      (x ∘ (insertionSwap i).symm) = 0
    rw [insertionSwap_symm,(hx _).2,mul_zero]

lemma insertionTerms_disjoint {N : ℕ} {T : FormVector (N+1)} (R : ℝ)
    (hc : ∀ x (j : Fin N), R ≤ ‖x j.castSucc‖ → FormZeroAt T x)
    (he : ∀ x, ‖x (Fin.last N)‖ < R → FormZeroAt T x) :
    FormsDisjoint (insertionTerm T) := by
  have hh (k l : Fin (N+1)) (hkl : k ≠ l) (x : Configuration (N+1)) :
      FormZeroAt (insertionTerm T k) x ∨ FormZeroAt (insertionTerm T l) x := by
    by_cases hk : ‖x k‖ < R
    · left
      exact insertionTerm_zero k (he _ (by simpa only [Function.comp_apply,insertionSwap_last] using hk))
    · right
      have hne : insertionSwap l k ≠ Fin.last N := by
        intro h
        have hh := congrArg (insertionSwap l) h
        exact hkl (by simpa only [insertionSwap,Equiv.swap_apply_self,Equiv.swap_apply_right] using hh)
      obtain ⟨j,hj⟩ := Fin.exists_castSucc_eq.mpr hne
      apply insertionTerm_zero l
      apply hc _ j
      simpa only [Function.comp_apply,hj,insertionSwap,Equiv.swap_apply_self] using le_of_not_gt hk
  constructor
  · intro k l hkl s x
    rcases hh k l hkl x with hk | hl
    · exact Or.inl (hk s).1
    · exact Or.inr (hl s).1
  · intro k l hkl s i a x
    rcases hh k l hkl x with hk | hl
    · exact Or.inl ((hk s).2 i a)
    · exact Or.inr ((hl s).2 i a)

lemma formMass_wedge {N : ℕ} {T : FormVector (N+1)} (hT : SobolevVector T)
    (hd : FormsDisjoint (insertionTerm T)) :
    formMass (wedgeForm T) = (N+1 : ℝ) * formMass T := by
  rw [wedgeForm,formMass_sum_disjoint (fun i => hT.insertionTerm i) hd]
  simp only [formMass_insertionTerm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]

lemma formEnergy_wedge {N : ℕ} {T : FormVector (N+1)} (hT : SobolevVector T)
    (hd : FormsDisjoint (insertionTerm T)) (Z : ℝ) :
    formEnergy Z (wedgeForm T) = (N+1 : ℝ) * formEnergy Z T := by
  rw [wedgeForm,formEnergy_sum_disjoint (fun i => hT.insertionTerm i) hd]
  simp only [formEnergy_insertionTerm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]

lemma tensor_zero_left {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    {x : Configuration (N+M)} (hx : FormZeroAt ψ (leftList x)) :
    FormZeroAt (tensorForm ψ φ) x := by
  intro s
  constructor
  · change ψ.value _ _ * _ = 0
    rw [(hx _).1,zero_mul]
  · intro i a
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    cases i with
    | inl i =>
      simp only [tensorForm,Equiv.symm_apply_apply,Sum.elim_inl,(hx _).2,zero_mul]
    | inr i =>
      simp only [tensorForm,Equiv.symm_apply_apply,Sum.elim_inr,(hx _).1,zero_mul]

lemma tensor_zero_right {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    {x : Configuration (N+M)} (hx : FormZeroAt φ (rightList x)) :
    FormZeroAt (tensorForm ψ φ) x := by
  intro s
  constructor
  · change _ * φ.value _ _ = 0
    rw [(hx _).1,mul_zero]
  · intro i a
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    cases i with
    | inl i =>
      simp only [tensorForm,Equiv.symm_apply_apply,Sum.elim_inl,(hx _).1,mul_zero]
    | inr i =>
      simp only [tensorForm,Equiv.symm_apply_apply,Sum.elim_inr,(hx _).2,mul_zero]

lemma tensor_insertion_disjoint {N : ℕ} (ψ : FormVector N) (φ : FormVector 1) (R : ℝ)
    (hc : ∀ x i, R ≤ ‖x i‖ → FormZeroAt ψ x)
    (he : ∀ x, ‖x 0‖ < R → FormZeroAt φ x) :
    FormsDisjoint (insertionTerm (tensorForm ψ φ)) := by
  apply insertionTerms_disjoint R
  · intro x i hx
    apply tensor_zero_left
    exact hc _ i hx
  · intro x hx
    apply tensor_zero_right
    exact he _ hx

theorem normalized_wedge_trial {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : FormAdmissible ψ) (hφ : FormAdmissible φ) (R : ℝ)
    (hc : ∀ x i, R ≤ ‖x i‖ → FormZeroAt ψ x)
    (he : ∀ x, ‖x 0‖ < R → FormZeroAt φ x) (Z : ℝ) :
    ∃ F : FormVector (N+1), FormAdmissible F ∧ formEnergy Z F = formEnergy Z (tensorForm ψ φ) := by
  let T := tensorForm ψ φ
  have hT := hψ.sobolevFermion.sobolevVector.tensor hφ.sobolevFermion.sobolevVector
  have hTa := tensor_coreAntisymmetric hψ.sobolevFermion φ
  have hd := tensor_insertion_disjoint ψ φ R hc he
  have hm : formMass T = 1 := by
    rw [formMass_tensor,formMass,formMass,hψ.2.2.2.2.1,hφ.2.2.2.2.1,one_mul]
  have hw := formMass_wedge hT hd
  rw [hm,mul_one] at hw
  have hp : 0 < formMass (wedgeForm T) := by rw [hw]; positivity
  refine ⟨scaleForm (Real.sqrt (formMass (wedgeForm T)))⁻¹ (wedgeForm T),
    (wedgeForm_fermion hT hTa).normalize hp,?_⟩
  rw [formEnergy_scale,formEnergy_wedge hT hd,hw,inv_pow,
    Real.sq_sqrt (le_of_lt (show (0:ℝ) < N+1 by positivity))]
  field_simp


open MeasureTheory Filter
open scoped BigOperators


def formKinetic {N : ℕ} (ψ : FormVector N) : ℝ :=
  (1/2:ℝ) * ∑ s, ∑ i, ∑ a, ∫ x, ‖ψ.gradient s i a x‖^2

def formNuclear {N : ℕ} (ψ : FormVector N) : ℝ :=
  ∑ s, ∑ i, ∫ x, ‖ψ.value s x‖^2 / ‖x i‖

def formRepulsion {N : ℕ} (ψ : FormVector N) : ℝ :=
  ∑ s, ∑ i, ∑ j, if i < j then ∫ x, ‖ψ.value s x‖^2 / ‖x i-x j‖ else 0

lemma formEnergy_parts {N : ℕ} (ψ : FormVector N) (Z : ℝ) :
    formEnergy Z ψ = formKinetic ψ - Z * formNuclear ψ + formRepulsion ψ := rfl

lemma formKinetic_nonneg {N : ℕ} (ψ : FormVector N) : 0 ≤ formKinetic ψ := by
  unfold formKinetic
  positivity

lemma formNuclear_nonneg {N : ℕ} (ψ : FormVector N) : 0 ≤ formNuclear ψ := by
  apply Finset.sum_nonneg; intro s _
  apply Finset.sum_nonneg; intro i _
  exact integral_nonneg fun x => div_nonneg (sq_nonneg _) (norm_nonneg _)

lemma integral_product_join {N M : ℕ} (f : Configuration N → ℝ) (g : Configuration M → ℝ) :
    (∫ z : Configuration (N+M), f (leftList z)*g (rightList z)) = (∫ x, f x)*(∫ y, g y) := by
  rw [← (configurationJoin_preserving N M).integral_comp
    (configurationJoin N M).toHomeomorph.measurableEmbedding]
  simp only [configurationJoin_apply_prod,leftList_join,rightList_join]
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul f g

lemma tensor_kinetic_left {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (i : Fin N) (a : Fin 3) :
    (∫ z, ‖(tensorForm ψ φ).gradient (joinLists s t) (finSumFinEquiv (Sum.inl i)) a z‖^2) =
      (∫ x, ‖ψ.gradient s i a x‖^2)*(∫ y, ‖φ.value t y‖^2) := by
  simp only [tensorForm,leftList_join,rightList_join,Equiv.symm_apply_apply,Sum.elim_inl,norm_mul,mul_pow]
  exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.gradient s i a x‖^2) (fun y => ‖φ.value t y‖^2)

lemma tensor_kinetic_right {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (i : Fin M) (a : Fin 3) :
    (∫ z, ‖(tensorForm ψ φ).gradient (joinLists s t) (finSumFinEquiv (Sum.inr i)) a z‖^2) =
      (∫ x, ‖ψ.value s x‖^2)*(∫ y, ‖φ.gradient t i a y‖^2) := by
  simp only [tensorForm,leftList_join,rightList_join,Equiv.symm_apply_apply,Sum.elim_inr,norm_mul,mul_pow]
  exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.value s x‖^2) (fun y => ‖φ.gradient t i a y‖^2)

lemma formKinetic_tensor {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) :
    formKinetic (tensorForm ψ φ) = formKinetic ψ * formMass φ + formMass ψ * formKinetic φ := by
  unfold formKinetic formMass
  rw [← sum_spin_join]
  have hk (s : Spins N) (t : Spins M) :
      (∑ i, ∑ a, ∫ z, ‖(tensorForm ψ φ).gradient (joinLists s t) i a z‖^2) =
      (∑ i, ∑ a, ∫ x, ‖ψ.gradient s i a x‖^2)*(∫ y, ‖φ.value t y‖^2) +
      (∫ x, ‖ψ.value s x‖^2)*(∑ i, ∑ a, ∫ y, ‖φ.gradient t i a y‖^2) := by
    rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
    simp only [tensor_kinetic_left,tensor_kinetic_right,Finset.sum_mul,Finset.mul_sum]
  simp_rw [hk,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
  ring

lemma tensor_nuclear_left {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (i : Fin N) :
    (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z (finSumFinEquiv (Sum.inl i))‖) =
      (∫ x, ‖ψ.value s x‖^2 / ‖x i‖)*(∫ y, ‖φ.value t y‖^2) := by
  change (∫ z, ‖ψ.value (leftList (joinLists s t)) (leftList z) *
    φ.value (rightList (joinLists s t)) (rightList z)‖^2 / ‖leftList z i‖) = _
  simp only [leftList_join,rightList_join,norm_mul,mul_pow]
  simp_rw [mul_div_right_comm]
  exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.value s x‖^2 / ‖x i‖) (fun y => ‖φ.value t y‖^2)

lemma tensor_nuclear_right {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (i : Fin M) :
    (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z (finSumFinEquiv (Sum.inr i))‖) =
      (∫ x, ‖ψ.value s x‖^2)*(∫ y, ‖φ.value t y‖^2 / ‖y i‖) := by
  change (∫ z, ‖ψ.value (leftList (joinLists s t)) (leftList z) *
    φ.value (rightList (joinLists s t)) (rightList z)‖^2 / ‖rightList z i‖) = _
  simp only [leftList_join,rightList_join,norm_mul,mul_pow,mul_div_assoc]
  exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.value s x‖^2) (fun y => ‖φ.value t y‖^2 / ‖y i‖)

lemma formNuclear_tensor {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) :
    formNuclear (tensorForm ψ φ) = formNuclear ψ * formMass φ + formMass ψ * formNuclear φ := by
  unfold formNuclear formMass
  rw [← sum_spin_join]
  have hk (s : Spins N) (t : Spins M) :
      (∑ i, ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i‖) =
      (∑ i, ∫ x, ‖ψ.value s x‖^2 / ‖x i‖)*(∫ y, ‖φ.value t y‖^2) +
      (∫ x, ‖ψ.value s x‖^2)*(∑ i, ∫ y, ‖φ.value t y‖^2 / ‖y i‖) := by
    rw [← Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
    simp only [tensor_nuclear_left,tensor_nuclear_right,Finset.sum_mul,Finset.mul_sum]
  simp_rw [hk,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]

lemma tensor_pair_left {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (i j : Fin N) :
    (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
      ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inl j))‖) =
      (∫ x, ‖ψ.value s x‖^2 / ‖x i-x j‖)*(∫ y, ‖φ.value t y‖^2) := by
  change (∫ z, ‖ψ.value (leftList (joinLists s t)) (leftList z) *
    φ.value (rightList (joinLists s t)) (rightList z)‖^2 / ‖leftList z i-leftList z j‖) = _
  simp only [leftList_join,rightList_join,norm_mul,mul_pow]
  simp_rw [mul_div_right_comm]
  exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.value s x‖^2 / ‖x i-x j‖) (fun y => ‖φ.value t y‖^2)

def tensorCross {N : ℕ} (ψ : FormVector N) (φ : FormVector 1) : ℝ :=
  ∑ s : Spins N, ∑ t : Spins 1, ∑ i : Fin N,
    ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i.castSucc-z (Fin.last N)‖

lemma formRepulsion_tensor_one {N : ℕ} (ψ : FormVector N) (φ : FormVector 1) :
    formRepulsion (tensorForm ψ φ) = formRepulsion ψ * formMass φ + tensorCross ψ φ := by
  classical
  unfold formRepulsion tensorCross formMass
  rw [← sum_spin_join]
  have hk (s : Spins N) (t : Spins 1) :
      (∑ i : Fin (N+1), ∑ j : Fin (N+1), if i < j then
        ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i-z j‖ else 0) =
      (∑ i : Fin N, ∑ j : Fin N, if i < j then ∫ x, ‖ψ.value s x‖^2 / ‖x i-x j‖ else 0)*
        (∫ y, ‖φ.value t y‖^2) +
      ∑ i : Fin N, ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
        ‖z i.castSucc-z (Fin.last N)‖ := by
    rw [Fin.sum_univ_castSucc]
    have he (i : Fin N) : (∑ j : Fin (N+1), if i.castSucc < j then
        ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i.castSucc-z j‖ else 0) =
        (∑ j : Fin N, if i < j then ∫ x, ‖ψ.value s x‖^2 / ‖x i-x j‖ else 0)*
          (∫ y, ‖φ.value t y‖^2) +
        ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i.castSucc-z (Fin.last N)‖ := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.castSucc_lt_castSucc_iff,Fin.castSucc_lt_last,ite_true]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      split_ifs
      · exact tensor_pair_left ψ φ s t i j
      · simp only [zero_mul]
    simp_rw [he,Finset.sum_add_distrib,← Finset.sum_mul]
    have he0 : (∑ j : Fin (N+1), if Fin.last N < j then
        ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z (Fin.last N)-z j‖ else 0) = 0 := by
      apply Finset.sum_eq_zero; intro j _
      exact ite_eq_right (not_lt_of_ge (Fin.le_last j))
    rw [he0,add_zero]
  simp_rw [hk,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

lemma formEnergy_tensor_one {N : ℕ} (ψ : FormVector N) (φ : FormVector 1) (Z : ℝ) :
    formEnergy Z (tensorForm ψ φ) = formEnergy Z ψ * formMass φ +
      formMass ψ * (formKinetic φ - Z * formNuclear φ) + tensorCross ψ φ := by
  rw [formEnergy_parts,formKinetic_tensor,formNuclear_tensor,formRepulsion_tensor_one,formEnergy_parts]
  ring


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
