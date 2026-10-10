import OAI.NumberTheory.CubicMoment.Estimates.FiniteMellinProduct
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! Passing an actual uniform finite-row moment through an integrable Mellin
weight. The proof is the triangle inequality in the finite Euclidean space. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem finite_row_integral_moment {Ω κ : Type*} [MeasurableSpace Ω]
    [Fintype κ] {μ : Measure Ω} (f : κ → Ω → ℂ) (w : Ω → ℂ)
    (hf : AEStronglyMeasurable (fun t => WithLp.toLp 2 (fun r => f r t)) μ)
    (hw : Integrable w μ) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ᵐ t ∂μ, (∑ r, ‖f r t‖^2) ≤ B) :
    (∑ r, ‖∫ t, w t*f r t ∂μ‖^2) ≤ (∫ t, ‖w t‖ ∂μ)^2*B := by
  let F : Ω → EuclideanSpace ℂ κ := fun t => WithLp.toLp 2 (fun r => f r t)
  let G : Ω → EuclideanSpace ℂ κ := fun t => w t • F t
  have hFn : ∀ᵐ t ∂μ, ‖F t‖ ≤ Real.sqrt B := by
    filter_upwards [hb] with t ht
    rw [EuclideanSpace.norm_eq]
    exact Real.sqrt_le_sqrt ht
  have hGn : ∀ᵐ t ∂μ, ‖G t‖ ≤ ‖w t‖*Real.sqrt B := by
    filter_upwards [hFn] with t ht
    dsimp [G]
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ht (_root_.norm_nonneg _)
  have hG : Integrable G μ := (hw.norm.mul_const (Real.sqrt B)).mono'
    (hw.aestronglyMeasurable.smul hf) hGn
  have hcoord (r : κ) : (∫ t, G t ∂μ) r = ∫ t, w t*f r t ∂μ := by
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : κ => ℂ) r).integral_comp_comm hG).symm
  have hbound : ‖∫ t, G t ∂μ‖ ≤ (∫ t, ‖w t‖ ∂μ)*Real.sqrt B := by
    apply (norm_integral_le_integral_norm G).trans
    rw [← integral_mul_const]
    exact integral_mono_ae hG.norm (hw.norm.mul_const _) hGn
  calc
    _ = ‖∫ t, G t ∂μ‖^2 := by rw [EuclideanSpace.norm_sq_eq]; simp_rw [hcoord]
    _ ≤ ((∫ t, ‖w t‖ ∂μ)*Real.sqrt B)^2 :=
      pow_le_pow_left₀ (_root_.norm_nonneg _) hbound 2
    _ = _ := by rw [mul_pow,Real.sq_sqrt hB]

theorem finite_interval_integral_moment {κ : Type*} [Fintype κ]
    (f : κ → ℝ → ℂ) (hf : ∀ r, Continuous (f r)) (w : ℝ → ℂ)
    (hw : Integrable w) (T B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ t ∈ Set.Icc (-T) T, (∑ r, ‖f r t‖^2) ≤ B) :
    (∑ r, ‖∫ t in Set.Icc (-T) T, w t*f r t‖^2) ≤
      (∫ t, ‖w t‖)^2*B := by
  have hc : Continuous (fun t => WithLp.toLp 2 (fun r => f r t)) :=
    (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp (continuous_pi hf)
  have ha : ∀ᵐ t ∂(volume.restrict (Set.Icc (-T) T)), (∑ r, ‖f r t‖^2) ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hb t ht
  have h := finite_row_integral_moment f w hc.aestronglyMeasurable hw.restrict hB ha
  apply h.trans
  have hm : (∫ t in Set.Icc (-T) T, ‖w t‖) ≤ ∫ t, ‖w t‖ :=
    setIntegral_le_integral hw.norm (Filter.Eventually.of_forall (fun _ => _root_.norm_nonneg _))
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (integral_nonneg (fun _ => _root_.norm_nonneg _)) hm 2) hB

end CubicFirstMoment

end

end OAI
