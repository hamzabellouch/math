import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarGroundTransform
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! A locally integrable planar function with zero distributional gradient
is constant almost everywhere. This is the uniqueness step needed after the
ground-state transform; it uses actual compact mollifiers. -/

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff
namespace ContinuumCoulomb

local instance instPlanarWeakConstantMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instPlanarWeakConstantBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instPlanarWeakConstantMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

def planarMollifier (k : ℕ) : ContDiffBump (0 : PlanarPosition) where
  rIn := 1/((k:ℝ)+1)
  rOut := 2/((k:ℝ)+1)
  rIn_pos := one_div_pos.mpr (by positivity)
  rIn_lt_rOut := div_lt_div_of_pos_right (by norm_num) (by positivity)

theorem planarMollifier_tendsto :
    Tendsto (fun k => (planarMollifier k).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [planarMollifier,mul_one_div,mul_zero] using h

private theorem planar_real_convolution_comm (f g : PlanarPosition → ℝ) :
    f ⋆ g = g ⋆ f := by
  ext x
  rw [convolution_eq_swap,convolution_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)

private theorem planar_reflected_derivative (κ : PlanarPosition → ℝ)
    (hκ : ContDiff ℝ ∞ κ) (x y e : PlanarPosition) :
    fderiv ℝ (fun z => κ (x-z)) y e = -(fderiv ℝ κ (x-y) e) := by
  have hd := ((hκ.differentiable (by simp) (x-y)).hasFDerivAt).comp y
    ((hasFDerivAt_id y).const_sub x)
  change HasFDerivAt (fun z => κ (x-z)) _ y at hd
  rw [hd.fderiv]
  simp

theorem planar_mollification_weak_zero (f : PlanarPosition → ℝ)
    (hf : LocallyIntegrable f)
    (hw : ∀ (φ : PlanarPosition → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ e, (∫ x, f x*fderiv ℝ φ x e) = 0) (k : ℕ) (x e : PlanarPosition) :
    fderiv ℝ ((planarMollifier k).normed volume ⋆ f) x e = 0 := by
  let κ := (planarMollifier k).normed volume
  have hκ : ContDiff ℝ ∞ κ := (planarMollifier k).contDiff_normed
  have hc : HasCompactSupport κ := (planarMollifier k).hasCompactSupport_normed
  have ht := hw (fun y => κ (x-y)) (hκ.comp (contDiff_const.sub contDiff_id))
    (hc.comp_homeomorph (Homeomorph.subLeft x)) e
  simp_rw [planar_reflected_derivative κ hκ x,mul_neg,integral_neg,neg_eq_zero] at ht
  rw [planar_real_convolution_comm κ f,
    (hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf (hκ.of_le (by simp)) x).fderiv,
    convolution_precompR_apply (lsmul ℝ ℝ) hf (hc.fderiv ℝ)
      (hκ.continuous_fderiv (by simp)) x e]
  simpa only [convolution_def,lsmul_apply,smul_eq_mul] using ht

theorem planar_weak_gradient_zero_constant (f : PlanarPosition → ℝ)
    (hf : LocallyIntegrable f)
    (hw : ∀ (φ : PlanarPosition → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ e, (∫ x, f x*fderiv ℝ φ x e) = 0) :
    ∃ c : ℝ, f =ᵐ[volume] fun _ => c := by
  let F (k : ℕ) : PlanarPosition → ℝ := (planarMollifier k).normed volume ⋆ f
  have hconst (k : ℕ) (x y : PlanarPosition) : F k x = F k y := by
    have hs : ContDiff ℝ ∞ (F k) :=
      (planarMollifier k).hasCompactSupport_normed.contDiff_convolution_left
        (lsmul ℝ ℝ) (planarMollifier k).contDiff_normed hf
    apply is_const_of_fderiv_eq_zero (hs.differentiable (by simp))
    intro z
    ext e
    exact planar_mollification_weak_zero f hf hw k z e
  have ht : ∀ᵐ x ∂volume, Tendsto (fun k => F k x) atTop (𝓝 (f x)) := by
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := planarMollifier) (K := 2) planarMollifier_tendsto _ hf
    exact Filter.Eventually.of_forall (fun k => by simp [planarMollifier,div_eq_mul_inv])
  obtain ⟨x,hx⟩ := ht.exists
  refine ⟨f x,?_⟩
  filter_upwards [ht] with y hy
  have he : (fun k => F k y) = (fun k => F k x) := funext (fun k => hconst k y x)
  rw [he] at hy
  exact tendsto_nhds_unique hy hx

end ContinuumCoulomb

end

end OAI
