import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.SlaterOccupation
import OAI.Analysis.Laughlin.Tensor.ExteriorAdjoint

namespace OAI

/-! The normalized determinant of finite Kronecker orbitals is the actual
antisymmetric coefficient tensor of an occupation basis vector. Substitution
of physical orbitals gives exactly the continuum Slater wave, also for every
complex superposition of occupations. -/

noncomputable section
namespace ContinuumCoulomb.FockSlaterTensor
open Laughlin Laughlin.Fock SlaterOccupation Coulomb
open scoped BigOperators

private lemma delta_product {n Q : ℕ} (b a : Laughlin.Configuration n Q) :
    (∏ i, if b i = a i then (1 : ℂ) else 0) = if b = a then 1 else 0 := by
  classical
  by_cases h : b = a
  · subst a
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

def basisTensor {Q n : ℕ} (S : Occupied Q n) : State n Q :=
  slaterWave (fun i j => if selection S i = j then 1 else 0)

lemma basisTensor_expansion {Q n : ℕ} (S : Occupied Q n) (a : Laughlin.Configuration n Q) :
    basisTensor S a = ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
      ∑ p : Equiv.Perm (Fin n), (((p.sign : ℤ) : ℂ)) *
        if (fun i => selection S (p i)) = a then 1 else 0 := by
  simp only [basisTensor, slaterWave, determinantWave_expansion, delta_product, Complex.ofReal_inv]

lemma basisTensor_antisymmetric {Q n : ℕ} (S : Occupied Q n) :
    Laughlin.Antisymmetric (basisTensor S) := by
  intro i j hij a
  simp only [basisTensor, slaterWave, determinantWave_permute,
    Equiv.Perm.sign_swap hij, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
  ring

lemma orderedWedge_selection {Q n : ℕ} (S : Occupied Q n) :
    orderedWedge (selection S) = occupationBasis Q S.val := by
  simp only [occupationBasis, ExteriorAlgebra.basis_apply_powersetCard,
    ExteriorAlgebra.ιMulti_family, selection, Function.comp_def, Pi.basisFun_apply,
    orderedWedge, mode]

lemma orderedWedge_perm {Q n : ℕ} (a : Laughlin.Configuration n Q) (p : Equiv.Perm (Fin n)) :
    orderedWedge (a ∘ p) = (((p.sign : ℤ) : ℂ)) • orderedWedge a := by
  simpa only [orderedWedge, Function.comp_def, Units.smul_def, Int.cast_smul_eq_zsmul] using
    (ExteriorAlgebra.ιMulti ℂ n).map_perm (fun i => mode (a i)) p

private lemma tensorExterior_deltas {I : Type*} [Fintype I] {Q n : ℕ}
    (c : I → ℂ) (b : I → Laughlin.Configuration n Q) :
    tensorExterior n Q (fun a => ∑ p, c p * if b p = a then 1 else 0) =
      ∑ p, c p • orderedWedge (b p) := by
  classical
  change (∑ a, (∑ p, c p * if b p = a then 1 else 0) • orderedWedge a) = _
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  simp

private lemma tensorExterior_scale {Q n : ℕ} (c : ℂ) (ψ : State n Q) :
    tensorExterior n Q (fun a => c * ψ a) = c • tensorExterior n Q ψ := by
  simp only [tensorExterior, Finset.smul_sum, smul_smul]

private lemma tensorExterior_basisTensor {Q n : ℕ} (S : Occupied Q n) :
    tensorExterior n Q (basisTensor S) =
      ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) •
        ((n.factorial : ℂ) • occupationBasis Q S.val) := by
  have he : basisTensor S = fun a => ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
      ∑ p : Equiv.Perm (Fin n), (((p.sign : ℤ) : ℂ)) *
        if (fun i => selection S (p i)) = a then 1 else 0 :=
    funext (basisTensor_expansion S)
  rw [he, tensorExterior_scale, tensorExterior_deltas]
  have hp (p : Equiv.Perm (Fin n)) :
      (((p.sign : ℤ) : ℂ)) • orderedWedge (fun i => selection S (p i)) =
        occupationBasis Q S.val := by
    change (((p.sign : ℤ) : ℂ)) • orderedWedge ((selection S) ∘ p) = _
    rw [orderedWedge_perm, smul_smul]
    have hs : (((p.sign : ℤ) : ℂ)) * (((p.sign : ℤ) : ℂ)) = 1 := by
      rcases Int.units_eq_one_or p.sign with h | h <;> simp [h]
    rw [hs, one_smul, orderedWedge_selection]
  simp only [hp, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]

lemma normalizedTensorExterior_basisTensor {Q n : ℕ} (S : Occupied Q n) :
    normalizedTensorExterior n Q (basisTensor S) = occupationBasis Q S.val := by
  have hp : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hs : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hp))
  have he : (Real.sqrt (n.factorial : ℝ) : ℂ)^2 = (n.factorial : ℂ) := by
    exact_mod_cast Real.sq_sqrt hp.le
  rw [normalizedTensorExterior, tensorExterior_basisTensor, smul_smul, smul_smul]
  have hc : ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
      ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) * (n.factorial : ℂ) = 1 := by
    rw [← he]
    field_simp
  rw [hc, one_smul]

lemma normalizedTensorReadout_basis {Q n : ℕ} (S : Occupied Q n) :
    normalizedTensorReadout n Q (occupationBasis Q S.val) = basisTensor S := by
  rw [← normalizedTensorExterior_basisTensor S]
  exact normalizedTensorReadout_left_inverse n Q _ (basisTensor_antisymmetric S)

def tensorValue {A : Type*} {Q n : ℕ} (v : Fin (Q + 1) → A → ℂ)
    (ψ : State n Q) (x : Fin n → A) : ℂ :=
  ∑ a : Laughlin.Configuration n Q, ψ a * ∏ i, v (a i) (x i)

lemma tensorValue_basisTensor {A : Type*} {Q n : ℕ} (v : Fin (Q + 1) → A → ℂ)
    (S : Occupied Q n) (x : Fin n → A) : tensorValue v (basisTensor S) x = wave v S x := by
  classical
  unfold wave slaterWave
  simp only [Complex.ofReal_inv]
  change (∑ a : Laughlin.Configuration n Q, basisTensor S a * ∏ i, v (a i) (x i)) =
    ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) * determinantWave (selectedOrbitals v S) x
  simp_rw [basisTensor_expansion, mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact (determinantWave_expansion (selectedOrbitals v S) x).symm

def occupationTensor {Q n : ℕ} (c : EuclideanSpace ℂ (Occupied Q n)) : State n Q :=
  fun a => ∑ S, c S * basisTensor S a

lemma occupationTensor_antisymmetric {Q n : ℕ} (c : EuclideanSpace ℂ (Occupied Q n)) :
    Laughlin.Antisymmetric (occupationTensor c) := by
  intro i j hij a
  simp only [occupationTensor, basisTensor_antisymmetric _ i j hij,
    mul_neg, Finset.sum_neg_distrib]

lemma normalizedTensorExterior_occupationTensor {Q n : ℕ}
    (c : EuclideanSpace ℂ (Occupied Q n)) :
    normalizedTensorExterior n Q (occupationTensor c) =
      ∑ S, c S • occupationBasis Q S.val := by
  unfold normalizedTensorExterior occupationTensor
  simp only [tensorExterior, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Finset.smul_sum]
  change ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) •
    (c S • tensorExterior n Q (basisTensor S)) = _
  rw [smul_comm]
  congr 1
  exact normalizedTensorExterior_basisTensor S

lemma tensorValue_occupationTensor {A : Type*} {Q n : ℕ}
    (v : Fin (Q + 1) → A → ℂ) (c : EuclideanSpace ℂ (Occupied Q n)) (x : Fin n → A) :
    tensorValue v (occupationTensor c) x = ∑ S, c S * wave v S x := by
  unfold tensorValue occupationTensor
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [← tensorValue_basisTensor v S x]
  unfold tensorValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

end ContinuumCoulomb.FockSlaterTensor

end

end OAI
