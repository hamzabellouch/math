import OAI.Analysis.KadisonKastler.HaarFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace OAI

/-! # The circle functional calculus of an actual unitary

The homomorphism needed by the Haar trace formula is constructed from
ordinary continuous functional calculus on the unitary's spectrum.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

/-- The unitary spectrum as a continuous map into the circle. -/
def unitarySpectrumCircle (u : unitary B) : C(spectrum ℂ (u : B), Circle) where
  toFun z := ⟨z.val, Unitary.spectrum_subset_circle u z.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Angular coordinates on the spectrum, taken in the quotient circle. -/
def unitarySpectrumAngle (u : unitary B) : C(spectrum ℂ (u : B), HaarCircle) :=
  (AddCircle.homeomorphCircle'.symm : C(Circle, HaarCircle)).comp (unitarySpectrumCircle u)

/-- Actual circle functional calculus in the supplied C*-algebra. -/
def unitaryCircleCFC (u : unitary B) : C(HaarCircle, ℂ) →⋆ₐ[ℂ] B :=
  (cfcHom (R := ℂ) (isStarNormal_of_mem_unitary u.property)).comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ (unitarySpectrumAngle u))

private theorem toCircle_eq_homeomorph (t : HaarCircle) :
    AddCircle.toCircle t = AddCircle.homeomorphCircle' t := by
  induction t using QuotientAddGroup.induction_on
  rename_i t
  rw [AddCircle.toCircle_apply_mk, AddCircle.homeomorphCircle'_apply_mk,
    div_self (by positivity : 2 * Real.pi ≠ 0), one_mul]

private theorem fourier_one_spectrum (u : unitary B) :
    (fourier (T := 2 * Real.pi) 1).comp (unitarySpectrumAngle u) =
      (ContinuousMap.id ℂ).restrict (spectrum ℂ (u : B)) := by
  ext z
  change fourier 1 (unitarySpectrumAngle u z) = z.val
  rw [fourier_one]
  change (AddCircle.toCircle (AddCircle.homeomorphCircle'.symm (unitarySpectrumCircle u z)) : ℂ) = z.val
  rw [toCircle_eq_homeomorph, AddCircle.homeomorphCircle'.apply_symm_apply]
  rfl

/-- The degree-one circle function evaluates to the original unitary. -/
theorem unitaryCircleCFC_fourier_one (u : unitary B) :
    unitaryCircleCFC u (fourier 1) = (u : B) := by
  change cfcHom (R := ℂ) (isStarNormal_of_mem_unitary u.property)
    ((fourier 1).comp (unitarySpectrumAngle u)) = _
  rw [fourier_one_spectrum, cfcHom_id]

private theorem fourier_add_map (u : unitary B) (k l : ℤ) :
    unitaryCircleCFC u (fourier (k + l)) =
      unitaryCircleCFC u (fourier k) * unitaryCircleCFC u (fourier l) := by
  rw [show fourier (T := 2 * Real.pi) (k + l) = fourier k * fourier l by
    ext t; exact fourier_add, map_mul]

private theorem unitaryCircleCFC_fourier_nat (u : unitary B) (n : ℕ) :
    unitaryCircleCFC u (fourier (n : ℤ)) = (u : B) ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, show fourier (T := 2 * Real.pi) 0 = 1 by ext t; exact fourier_zero]
    simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, fourier_add_map, ih, unitaryCircleCFC_fourier_one, pow_succ]

/-- Every integer Fourier monomial evaluates to the corresponding actual
unitary power, supplying the hypothesis of the continuous Haar formula. -/
theorem unitaryCircleCFC_fourier (u : unitary B) (n : ℤ) :
    unitaryCircleCFC u (fourier n) = haarPower u n := by
  cases n with
  | ofNat n =>
    change unitaryCircleCFC u (fourier (n : ℤ)) = haarPower u (n : ℤ)
    rw [haarPower_natCast]
    exact unitaryCircleCFC_fourier_nat u n
  | negSucc n =>
    have hn : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
    rw [hn, haarPower_neg, haarPower_natCast]
    have hneg : fourier (T := 2 * Real.pi) (-((n + 1 : ℕ) : ℤ)) =
        star (fourier ((n + 1 : ℕ) : ℤ)) := by
      ext t
      simpa only [ContinuousMap.star_apply, starRingEnd_apply] using
        (fourier_neg (T := 2 * Real.pi) (n := ((n + 1 : ℕ) : ℤ)) (x := t))
    rw [hneg, map_star, unitaryCircleCFC_fourier_nat]

/-- Haar moments alone determine the trace of the constructed circle
functional calculus, without an additional representation hypothesis. -/
theorem trace_unitaryCircleCFC (τ : FaithfulTracialState B) (u : unitary B)
    (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower u k) = 0)
    (g : C(HaarCircle, ℂ)) :
    τ.toLinearMap (unitaryCircleCFC u g) = haarCircleIntegral g := by
  rw [haarCircleIntegral_apply]
  exact haar_functional_trace τ u hhaar (unitaryCircleCFC u) (unitaryCircleCFC_fourier u) g

end

end KadisonKastler

end OAI
