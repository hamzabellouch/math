import OAI.Analysis.KadisonKastler.SpectralClipping
import OAI.Analysis.KadisonKastler.BlockMatrices
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

namespace OAI

/-! # Adjoint compatibility of the continuous spectral cutoff

A two-by-two block argument transports continuous functional calculus
through an intertwiner between selfadjoint elements. Applied twice to
`xx*` and `x*x`, it shows that the cutoff commutes with adjoints. This
provides the left-sided fourth-moment estimate from the right-sided one.
-/

namespace KadisonKastler

noncomputable section

open scoped CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance clipPiComplexCFC : ContinuousFunctionalCalculus ℂ (Fin 2 → A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus
local instance clipBlockComplexCFC :
    ContinuousFunctionalCalculus ℂ (CStarMatrix (Fin 2) (Fin 2) A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus
local instance clipPiCFC : ContinuousFunctionalCalculus ℝ (Fin 2 → A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus
local instance clipBlockCFC :
    ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin 2) (Fin 2) A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

local instance clipBlockOrder : PartialOrder (CStarMatrix (Fin 2) (Fin 2) A) :=
  CStarAlgebra.spectralOrder _
local instance clipBlockStarOrder : StarOrderedRing (CStarMatrix (Fin 2) (Fin 2) A) :=
  CStarAlgebra.spectralOrderedRing _

private theorem cfc_blockDiagonal (f : ℝ → ℝ) (hf : Continuous f)
    (a b : A) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    cfc f (blockDiagonal a b) = blockDiagonal (cfc f a) (cfc f b) := by
  have hp : IsSelfAdjoint (![a, b] : Fin 2 → A) := by
    funext i
    fin_cases i
    · change star a = a
      exact ha.star_eq
    · change star b = b
      exact hb.star_eq
  have hpd : IsSelfAdjoint (diagonalStarAlgHom (Fin 2) (![a, b] : Fin 2 → A)) := by
    change star (diagonalStarAlgHom (Fin 2) (![a, b] : Fin 2 → A)) = _
    rw [← map_star, hp.star_eq]
  have hc : Continuous (diagonalStarAlgHom (A := A) (Fin 2)) :=
    (NonUnitalStarAlgHom.isometry (diagonalStarAlgHom (A := A) (Fin 2))
      (diagonalStarAlgHom_injective (Fin 2))).continuous
  have hm := (diagonalStarAlgHom (A := A) (Fin 2)).map_cfc f (![a, b] : Fin 2 → A)
    hf.continuousOn hc hp hpd
  rw [blockDiagonal, ← hm]
  have he := cfc_map_pi (S := ℂ) f (![a, b] : Fin 2 → A) hf.continuousOn hp
    (by intro i; fin_cases i; exact ha; exact hb)
  rw [he]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Continuous real functional calculus respects an intertwiner of two
selfadjoint elements. -/
theorem cfc_selfAdjoint_intertwines (a b x : A)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hx : a * x = x * b)
    (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f a * x = x * cfc f b := by
  let D : CStarMatrix (Fin 2) (Fin 2) A := blockDiagonal a b
  let X : CStarMatrix (Fin 2) (Fin 2) A := blockOffDiagonal x 0
  have hDX : Commute D X := by
    change D * X = X * D
    ext i j
    simp only [D, X, CStarMatrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [blockDiagonal, blockOffDiagonal, hx]
  have hfc := hDX.cfc_real f
  rw [show D = blockDiagonal a b from rfl, cfc_blockDiagonal f hf a b ha hb] at hfc
  have he := congrArg (fun T : CStarMatrix (Fin 2) (Fin 2) A => T 0 1) hfc.eq
  simp only [CStarMatrix.mul_apply, Fin.sum_univ_two, X] at he
  simpa [blockDiagonal, blockOffDiagonal] using he

/-- The absolute values satisfy the usual polar intertwining identity,
without requiring the existence of a polar partial isometry. -/
theorem abs_star_intertwines (x : A) : CFC.abs (star x) * x = x * CFC.abs x := by
  have h := cfc_selfAdjoint_intertwines (x * star x) (star x * x) x
    (by simpa only [star_star] using (star_mul_self_nonneg (star x)).isSelfAdjoint)
    (star_mul_self_nonneg x).isSelfAdjoint (by noncomm_ring)
    Real.sqrt Real.continuous_sqrt
  simp only [CFC.abs, star_star]
  rw [CFC.sqrt_eq_real_sqrt _ (by simpa only [star_star] using star_mul_self_nonneg (star x)),
    CFC.sqrt_eq_real_sqrt _ (star_mul_self_nonneg x), cfcₙ_eq_cfc, cfcₙ_eq_cfc]
  exact h

/-- Clipping an adjoint is the adjoint of the same continuous cutoff. -/
theorem star_spectralClip {β : ℝ} (hβ : 0 < β) (x : A) :
    star (spectralClip β x) = spectralClip β (star x) := by
  have h := cfc_selfAdjoint_intertwines (CFC.abs (star x)) (CFC.abs x) x
    (CFC.abs_nonneg _).isSelfAdjoint (CFC.abs_nonneg _).isSelfAdjoint
    (abs_star_intertwines x) (clippingFunction β) (clippingFunction_continuous hβ)
  have hs := congrArg star h
  have hr : star (cfc (clippingFunction β) (CFC.abs x)) =
      cfc (clippingFunction β) (CFC.abs x) :=
    (cfc_predicate (clippingFunction β) (CFC.abs x)).star_eq
  have hl : star (cfc (clippingFunction β) (CFC.abs (star x))) =
      cfc (clippingFunction β) (CFC.abs (star x)) :=
    (cfc_predicate (clippingFunction β) (CFC.abs (star x))).star_eq
  simp only [star_mul, hr, hl] at hs
  simpa only [spectralClip, star_mul, hr] using hs.symm

end

end KadisonKastler

end OAI
