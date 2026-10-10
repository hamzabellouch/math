import OAI.Analysis.KadisonKastler.HardyKernelVectors
import OAI.Analysis.KadisonKastler.SpectralCommutant

namespace OAI

/-! # The reproducing row on the positive-frequency space -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def hardyKernelRow (z : ℂ) (hz : 0 < z.re) : RegularCoreHilbert H →L[ℂ] H :=
  (hardyKernelInclusion z hz).toContinuousLinearMap.adjoint

theorem hardyKernelRow_inclusion (z : ℂ) (hz : 0 < z.re) (x : H) :
    hardyKernelRow z hz (hardyKernelInclusion z hz x) = x :=
  congrArg (fun T : H →L[ℂ] H => T x) (hardyKernelInclusion_adjoint_self z hz)

theorem hardyKernelRow_projection (z : ℂ) (hz : 0 < z.re) (f : RegularCoreHilbert H) :
    hardyKernelRow z hz (regularFrequencyProjection 0 f) = hardyKernelRow z hz f := by
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x ((hardyKernelInclusion z hz).toContinuousLinearMap.adjoint
    (regularFrequencyProjection 0 f)) = inner ℂ x
      ((hardyKernelInclusion z hz).toContinuousLinearMap.adjoint f)
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  have hs : inner ℂ (regularFrequencyProjection 0 (hardyKernelInclusion z hz x)) f =
      inner ℂ (hardyKernelInclusion z hz x) (regularFrequencyProjection 0 f) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (regularFrequencyProjection_isStarProjection (H := H) 0).isSelfAdjoint)
      (hardyKernelInclusion z hz x) f
  rw [hardyKernelInclusion_positive] at hs
  exact hs.symm

theorem regularCharacter_adjoint_neg (b : ℝ) :
    (regularCharacterUnitary (H := H) (2 * Real.pi * b) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H).adjoint =
    (regularCharacterUnitary (H := H) (2 * Real.pi * (-b)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  have h := congrArg (fun u : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =>
    (u : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (regularCharacterUnitary_neg (H := H) (2 * Real.pi * b))
  simpa only [Unitary.coe_star, mul_neg] using h.symm

/-- Positive character shifts have the expected scalar action under evaluation. -/
theorem hardyKernelRow_forward (z : ℂ) (hz : 0 < z.re) {b : ℝ} (hb : 0 ≤ b)
    (f : RegularCoreHilbert H) (hf : regularFrequencyProjection 0 f = f) :
    hardyKernelRow z hz ((regularCharacterUnitary (H := H) (2 * Real.pi * b) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
      star (Complex.exp (-z * b)) • hardyKernelRow z hz f := by
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x ((hardyKernelInclusion z hz).toContinuousLinearMap.adjoint _) = _
  rw [ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.adjoint_inner_left, regularCharacter_adjoint_neg]
  let g := (regularCharacterUnitary (H := H) (2 * Real.pi * (-b)) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)
  have hs : inner ℂ (regularFrequencyProjection 0 g) f =
      inner ℂ g (regularFrequencyProjection 0 f) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (regularFrequencyProjection_isStarProjection (H := H) 0).isSelfAdjoint) g f
  dsimp [g] at hs
  rw [hf, hardyKernelInclusion_backward_shift z hz hb] at hs
  change inner ℂ ((regularCharacterUnitary (H := H) (2 * Real.pi * (-b)) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)) f = _
  rw [← hs, inner_smul_left, inner_smul_right]
  change star (Complex.exp (-z * b)) *
    inner ℂ (hardyKernelInclusion z hz x) f =
      star (Complex.exp (-z * b)) * inner ℂ x
        ((hardyKernelInclusion z hz).toContinuousLinearMap.adjoint f)
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

end

end KadisonKastler

end OAI
