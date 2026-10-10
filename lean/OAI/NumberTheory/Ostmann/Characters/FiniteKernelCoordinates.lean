import OAI.NumberTheory.Ostmann.Characters.FiniteKernelBlocks

namespace OAI

/-! # Literal residue-point coordinates of the local kernel matrix -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def residuePointVector {p : ℕ} (a x : ZMod p) : ℂ :=
  if x = a then 1 else 0

theorem centeredSupportProjection_sum {α : Type*}
    (S : Finset α) (f : α → ℂ) :
    (∑ x ∈ S, centeredSupportProjection S f x) = 0 := by
  have he : (∑ x ∈ S, centeredSupportProjection S f x) =
      (∑ x ∈ S, f x) - (S.card : ℂ) * finiteSupportMean S f := by
    simp only [centeredSupportProjection]
    rw [Finset.sum_congr rfl (fun x hx => ite_eq_left hx), Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [he, finiteSupportMean_spec, sub_self]

theorem centeredSupportProjection_idempotent {α : Type*}
    (S : Finset α) (f : α → ℂ) :
    centeredSupportProjection S (centeredSupportProjection S f) = centeredSupportProjection S f := by
  have hm : finiteSupportMean S (centeredSupportProjection S f) = 0 := by
    rw [finiteSupportMean, centeredSupportProjection_sum, mul_zero]
  funext x
  by_cases hx : x ∈ S
  · simp only [centeredSupportProjection, ite_eq_left hx, hm, sub_zero]
  · simp only [centeredSupportProjection, ite_eq_right hx]

theorem uniformResidueVector_ite {p : ℕ} (S : Finset (ZMod p)) (x : ZMod p) :
    uniformResidueVector S x = if x ∈ S then (S.card : ℂ)⁻¹ else 0 := by
  by_cases hx : x ∈ S <;> simp [uniformResidueVector, hx]

theorem residuePointVector_decomposition {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (a : ZMod p) (ha : a ∈ S) :
    residuePointVector a = fun x => uniformResidueVector S x +
      centeredSupportProjection S (residuePointVector a) x := by
  have hm : finiteSupportMean S (residuePointVector a) = (S.card : ℂ)⁻¹ := by
    simp [finiteSupportMean, residuePointVector, ha]
  funext x
  by_cases hx : x ∈ S
  · simp only [uniformResidueVector_ite, centeredSupportProjection, ite_eq_left hx, hm]
    ring
  · have hxa : x ≠ a := by intro h; subst x; exact hx ha
    simp only [residuePointVector, ite_eq_right hxa, uniformResidueVector_ite,
      ite_eq_right hx, centeredSupportProjection, add_zero]

theorem rawAdditiveKernelAction_add_input {p : ℕ} [NeZero p]
    (k f g : ZMod p → ℂ) :
    rawAdditiveKernelAction k (fun x => f x + g x) =
      fun x => rawAdditiveKernelAction k f x + rawAdditiveKernelAction k g x := by
  funext x
  simp only [rawAdditiveKernelAction, add_mul, Finset.sum_add_distrib]

theorem residuePointVector_kernel {p : ℕ} [NeZero p]
    (k : ZMod p → ℂ) (a b : ZMod p) :
    (∑ x, conj (residuePointVector a x) * rawAdditiveKernelAction k (residuePointVector b) x) =
      k (a - b) := by
  simp [residuePointVector, rawAdditiveKernelAction]

end Ostmann

end OAI
