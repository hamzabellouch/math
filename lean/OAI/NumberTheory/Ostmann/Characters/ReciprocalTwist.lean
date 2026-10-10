import OAI.NumberTheory.Ostmann.Characters.AffineMean

namespace OAI

/-!
# The reciprocal twist used in the uniform Mellin estimate

Inversion preserves the finite-field squared norm. The mean of the
reciprocal twist is exactly an additive Fourier coefficient of the
original multiplicatively twisted test.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def reciprocalTwist {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ) (a x : ZMod p) : ℂ :=
  g x⁻¹ * η x⁻¹ * ZMod.stdAddChar (-(a * x⁻¹))

theorem reciprocalTwist_zero {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (η : MulChar (ZMod p) ℂ) (a : ZMod p) :
    reciprocalTwist g η a 0 = 0 := by
  simp only [reciprocalTwist, inv_zero, hg, zero_mul]

theorem norm_reciprocalTwist {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (η : MulChar (ZMod p) ℂ) (a x : ZMod p) :
    ‖reciprocalTwist g η a x‖ = ‖g x⁻¹‖ := by
  by_cases hx : x = 0
  · simp only [hx, reciprocalTwist_zero g hg, inv_zero, hg, norm_zero]
  · have hη : ‖η x⁻¹‖ = 1 :=
      norm_mulChar_unit η (Units.mk0 x⁻¹ (inv_ne_zero hx))
    simp only [reciprocalTwist, norm_mul, hη, mul_one]
    simp [ZMod.stdAddChar_apply]

theorem reciprocalTwist_energy {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (η : MulChar (ZMod p) ℂ) (a : ZMod p) :
    (∑ x : ZMod p, ‖reciprocalTwist g η a x‖ ^ 2) = ∑ x : ZMod p, ‖g x‖ ^ 2 := by
  simp_rw [norm_reciprocalTwist g hg]
  exact (Equiv.inv (ZMod p)).bijective.sum_comp (fun x : ZMod p => ‖g x‖ ^ 2)

theorem reciprocalTwist_mean {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ) (a : ZMod p) :
    fieldMean (reciprocalTwist g η a) = additiveFourier (fun x => g x * η x) a := by
  rw [fieldMean_eq_sum, additiveFourier_apply]
  congr 1
  have h := (Equiv.inv (ZMod p)).bijective.sum_comp
    (fun x : ZMod p => g x * η x * ZMod.stdAddChar (-(a * x)))
  change (∑ x : ZMod p, g x⁻¹ * η x⁻¹ * ZMod.stdAddChar (-(a * x⁻¹))) =
    ∑ x : ZMod p, g x * η x * ZMod.stdAddChar (-(a * x)) at h
  simpa only [reciprocalTwist, mul_comm a] using h

end Ostmann

end OAI
