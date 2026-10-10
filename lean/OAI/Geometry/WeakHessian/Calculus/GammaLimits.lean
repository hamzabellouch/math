import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.AbsGammaLipschitz

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile16
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

lemma memLp_gamma_lipschitz (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u φ : X → ℝ} (hu : Sobolev m u)
    {L : ℝ≥0} (hφ : LipschitzWith L φ) : MemLp (gamma m u φ) 2 m :=
  (hu.2.2.const_mul (L:ℝ)).mono'
    (gamma_aestronglyMeasurable hfin hu.2.1 (localSobolev_of_lipschitz hfin hφ))
    (by simpa only [Real.norm_eq_abs] using abs_gamma_lipschitz_le hfin hpar hu.2.1 hφ)

lemma norm_gamma_lipschitz_le (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u φ : X → ℝ} (hu : Sobolev m u)
    {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    ‖(memLp_gamma_lipschitz hfin hpar hu hφ).toLp (gamma m u φ)‖ ≤
      (L:ℝ)*‖hu.2.2.toLp (weakGradient m u)‖ := by
  have H : ‖(memLp_gamma_lipschitz hfin hpar hu hφ).toLp (gamma m u φ)‖ ≤
      ‖(hu.2.2.const_mul (L:ℝ)).toLp (fun x => (L:ℝ)*weakGradient m u x)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(memLp_gamma_lipschitz hfin hpar hu hφ).coeFn_toLp,
      (hu.2.2.const_mul (L:ℝ)).coeFn_toLp,abs_gamma_lipschitz_le hfin hpar hu.2.1 hφ] with x hx hy hz
    rw [hx,hy,Real.norm_eq_abs,Real.norm_eq_abs]
    exact hz.trans (le_abs_self _)
  have he : (hu.2.2.const_mul (L:ℝ)).toLp (fun x => (L:ℝ)*weakGradient m u x) =
      (L:ℝ) • hu.2.2.toLp (weakGradient m u) := by
    exact MemLp.toLp_const_smul (L:ℝ) hu.2.2
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg L.coe_nonneg] at H
  exact H

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma abs_integral_mul_le_L2_norm {a b : X → ℝ} (ha : MemLp a 2 m) (hb : MemLp b 2 m) :
    |∫ x,a x*b x ∂m| ≤ ‖ha.toLp a‖*‖hb.toLp b‖ := by
  have H : (∫ x,a x*b x ∂m) = ⟪ha.toLp a,hb.toLp b⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp,hb.coeFn_toLp] with x hx hy
    simp only [hx,hy,RCLike.inner_apply,conj_trivial,mul_comm]
  rw [H]
  exact abs_real_inner_le_norm _ _

lemma abs_weighted_gamma_lipschitz_le (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {a u φ : X → ℝ} (ha : MemLp a 2 m)
    (hu : Sobolev m u) {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    |∫ x,a x*gamma m u φ x ∂m| ≤
      (L:ℝ)*‖ha.toLp a‖*‖hu.2.2.toLp (weakGradient m u)‖ := by
  have H := (abs_integral_mul_le_L2_norm ha (memLp_gamma_lipschitz hfin hpar hu hφ)).trans
    (mul_le_mul_of_nonneg_left (norm_gamma_lipschitz_le hfin hpar hu hφ) (norm_nonneg _))
  simpa only [mul_left_comm (‖ha.toLp a‖) (L:ℝ),mul_assoc] using H

lemma weighted_gamma_root_difference_bound (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u v φ : X → ℝ}
    (hu : Sobolev m u) (hv : Sobolev m v) {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    |(∫ x,u x*gamma m u φ x ∂m)-(∫ x,v x*gamma m v φ x ∂m)| ≤
      (L:ℝ)*‖(hu.1.sub hv.1).toLp (fun x => u x-v x)‖*‖hu.2.2.toLp (weakGradient m u)‖+
      (L:ℝ)*‖hv.1.toLp v‖*‖(hu.sub hfin hv).2.2.toLp (weakGradient m (fun x => u x-v x))‖ := by
  let hsub := hu.sub hfin hv
  have h1 := hu.1.integrable_mul (memLp_gamma_lipschitz hfin hpar hu hφ)
  have h2 := hv.1.integrable_mul (memLp_gamma_lipschitz hfin hpar hv hφ)
  have h3 := (hu.1.sub hv.1).integrable_mul (memLp_gamma_lipschitz hfin hpar hu hφ)
  have h4 := hv.1.integrable_mul (memLp_gamma_lipschitz hfin hpar hsub hφ)
  have he : (∫ x,u x*gamma m u φ x ∂m)-(∫ x,v x*gamma m v φ x ∂m) =
      (∫ x,(u x-v x)*gamma m u φ x ∂m)+(∫ x,v x*gamma m (fun y => u y-v y) φ x ∂m) := by
    change (∫ x,(u * gamma m u φ) x ∂m)-(∫ x,(v * gamma m v φ) x ∂m) =
      (∫ x,((u-v)*gamma m u φ) x ∂m)+(∫ x,(v*gamma m (fun y => u y-v y) φ) x ∂m)
    rw [← integral_sub h1 h2,← integral_add h3 h4]
    apply integral_congr_ae
    filter_upwards [gamma_sub_left hfin hpar hu.2.1 hv.2.1 (localSobolev_of_lipschitz hfin hφ)] with x hx
    simp only [Pi.mul_apply,Pi.sub_apply]
    rw [hx]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_weighted_gamma_lipschitz_le hfin hpar (hu.1.sub hv.1) hu hφ)
    (abs_weighted_gamma_lipschitz_le hfin hpar hv.1 hsub hφ))
end WeakHessian

end
end InlinedFile16

end OAI
