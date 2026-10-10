import OAI.Analysis.IrrationalRotation.Model.Spectral
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

namespace OAI

noncomputable section
open scoped CStarAlgebra ComplexOrder
namespace Invariant233.TracialState

variable {A : Type*} [CStarAlgebra A]

local instance tracialStateBoundsSpectralOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance tracialStateBoundsSpectralOrderedRing : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

theorem positive_of_nonneg (τ : TracialState A) {a : A} (ha : 0 ≤ a) :
    0 ≤ τ a := by
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  apply RCLike.nonneg_iff.mpr
  refine ⟨τ.positive b, ?_⟩
  apply Complex.conj_eq_iff_im.mp
  change star (τ (star b * b)) = τ (star b * b)
  rw [← τ.map_star]
  simp only [star_mul, star_star]

def toPositiveLinearMap (τ : TracialState A) : A →ₚ[ℂ] ℂ where
  toLinearMap := τ.toContinuousLinearMap.toLinearMap
  monotone' := by
    intro a b hab
    have h := τ.positive_of_nonneg (sub_nonneg.mpr hab)
    change 0 ≤ τ.toContinuousLinearMap (b - a) at h
    rw [map_sub] at h
    exact sub_nonneg.mp h

@[simp] theorem toPositiveLinearMap_apply (τ : TracialState A) (a : A) :
    τ.toPositiveLinearMap a = τ a := rfl

theorem cauchySchwarz (τ : TracialState A) (a b : A) :
    ‖τ (star a * b)‖ ^ 2 ≤ (τ (star a * a)).re * (τ (star b * b)).re := by
  let f := τ.toPositiveLinearMap
  have h := norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS a) (f.toPreGNS b)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [mul_pow, PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.preGNS_norm_def] at hs
  change ‖τ (star a * b)‖ ^ 2 ≤
    (Real.sqrt (τ (star a * a)).re) ^ 2 * (Real.sqrt (τ (star b * b)).re) ^ 2 at hs
  rwa [Real.sq_sqrt (τ.positive a), Real.sq_sqrt (τ.positive b)] at hs

theorem norm_apply_le (τ : TracialState A) (a : A) : ‖τ a‖ ≤ ‖a‖ := by
  have hcs := τ.cauchySchwarz 1 a
  simp only [star_one, one_mul, τ.map_one, Complex.one_re, one_mul] at hcs
  have hb := τ.toPositiveLinearMap.norm_apply_le_of_nonneg
    (star a * a) (star_mul_self_nonneg a)
  simp only [toPositiveLinearMap_apply, τ.map_one, norm_one, one_mul,
    CStarRing.norm_star_mul_self] at hb
  have hre := (Complex.re_le_norm (τ (star a * a))).trans hb
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith

theorem norm_eq_one (τ : TracialState A) : ‖τ.toContinuousLinearMap‖ = 1 := by
  have hnontrivial : Nontrivial A := by
    apply not_subsingleton_iff_nontrivial.mp
    intro h
    have h01 : (0 : A) = 1 := Subsingleton.elim _ _
    have hbad := congrArg τ.toContinuousLinearMap h01
    simp only [map_zero, τ.map_one] at hbad
    exact zero_ne_one hbad
  let := hnontrivial
  apply le_antisymm
  · exact τ.toContinuousLinearMap.opNorm_le_bound (by norm_num)
      (fun a => by simpa only [one_mul] using τ.norm_apply_le a)
  · have h := τ.toContinuousLinearMap.le_opNorm (1 : A)
    simpa only [τ.map_one, norm_one, mul_one] using h

end Invariant233.TracialState

end

end OAI
