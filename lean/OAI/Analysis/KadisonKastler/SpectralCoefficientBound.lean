import OAI.Analysis.KadisonKastler.CornerSpectralWitness
import OAI.Analysis.KadisonKastler.ProjectionNormGap

namespace OAI

/-! Turning the positive spectral-cut inequality into a lower bound on
the actual represented vectors. -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace
open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance spectralCoefficientOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance spectralCoefficientPreorder : Preorder (Algebra M) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralCoefficientLE : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance spectralCoefficientStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem projection_inner_eq_norm_sq (P : H →L[ℂ] H) (hP : IsStarProjection P) (ξ : H) :
    inner ℂ ξ (P ξ) = (‖P ξ‖ ^ 2 : ℝ) := by
  have hs : P.adjoint = P := hP.isSelfAdjoint.star_eq
  have hi : P (P ξ) = P ξ := congrArg (fun T : H →L[ℂ] H => T ξ) hP.isIdempotentElem.eq
  have he := P.adjoint_inner_right ξ (P ξ)
  rw [hs, hi, inner_self_eq_norm_sq_to_K] at he
  simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using he

theorem spectral_lower_bound_on_vectors (p : AlgebraProjection M) (b : Algebra M)
    {t : ℝ} (ht : t • p.val ≤ p.val * (star b * b) * p.val) (ξ : H) :
    t * ‖(p.val : H →L[ℂ] H) ξ‖ ^ 2 ≤
      ‖(b : H →L[ℂ] H) ((p.val : H →L[ℂ] H) ξ)‖ ^ 2 := by
  let P : H →L[ℂ] H := p.val
  let B : H →L[ℂ] H := b
  have hP : IsStarProjection P := p.property.map M.toStarSubalgebra.subtype
  have hs : P.adjoint = P := hP.isSelfAdjoint.star_eq
  have hp : 0 ≤ P * (star B * B) * P - t • P := by
    have h := map_nonneg M.toStarSubalgebra.subtype (sub_nonneg.mpr ht)
    exact h
  have htest := (ContinuousLinearMap.nonneg_iff_isPositive.mp hp).re_inner_nonneg_right ξ
  have hfirst : inner ℂ ξ ((P * (star B * B) * P) ξ) =
      (‖B (P ξ)‖ ^ 2 : ℝ) := by
    change inner ℂ ξ (P (B.adjoint (B (P ξ)))) = _
    calc
      _ = inner ℂ (P.adjoint ξ) (B.adjoint (B (P ξ))) :=
        (P.adjoint_inner_left _ _).symm
      _ = inner ℂ (P ξ) (B.adjoint (B (P ξ))) := by rw [hs]
      _ = inner ℂ (B (P ξ)) (B (P ξ)) := B.adjoint_inner_right _ _
      _ = _ := by
        simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
          Complex.ofReal_pow]
  have he : inner ℂ ξ ((P * (star B * B) * P - t • P) ξ) =
      (‖B (P ξ)‖ ^ 2 : ℝ) - (t : ℂ) * (‖P ξ‖ ^ 2 : ℝ) := by
    rw [sub_apply, inner_sub_right, hfirst]
    change _ - inner ℂ ξ ((t : ℂ) • P ξ) = _
    rw [inner_smul_right, projection_inner_eq_norm_sq P hP ξ]
  change 0 ≤ (inner ℂ ξ ((P * (star B * B) * P - t • P) ξ)).re at htest
  rw [he] at htest
  have hreal : 0 ≤ ‖B (P ξ)‖ ^ 2 - t * ‖P ξ‖ ^ 2 := by
    simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] using htest
  exact sub_nonneg.mp hreal

end

end KadisonKastler

end OAI
