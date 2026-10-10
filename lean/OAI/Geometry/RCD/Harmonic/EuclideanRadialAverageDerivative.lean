import OAI.Geometry.RCD.Harmonic.EuclideanRadialWeight
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! # Differentiating a compactly supported radial average -/

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology

noncomputable section
namespace RegularPointCoordinates

/-- A global C² compact extension permits differentiation in the averaging
radius with an integrable bound independent of that radius. -/
theorem hasDerivAt_radial_average {n : ℕ} {f : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) (p : Euclidean n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x, f (p+s • x)*euclideanRadialWeight n x)
      (∫ x, fderiv ℝ f (p+t • x) x*euclideanRadialWeight n x) t := by
  let ρ := euclideanRadialWeight n
  have hρ : Continuous ρ := (euclideanRadialWeight_smooth n).continuous
  have hρs : HasCompactSupport ρ := euclideanRadialWeight_compact n
  have hdf := hf.continuous_fderiv (by norm_num)
  obtain ⟨C,hC⟩ := hdf.bounded_above_of_compact_support (hfs.fderiv ℝ)
  have hF (s : ℝ) : Continuous (fun x => f (p+s • x)*ρ x) :=
    (hf.continuous.comp (continuous_const.add (continuous_const_smul s))).mul hρ
  have hD (s : ℝ) : Continuous (fun x => fderiv ℝ f (p+s • x) x*ρ x) :=
    ((hdf.comp (continuous_const.add (continuous_const_smul s))).clm_apply continuous_id).mul hρ
  have hderiv (x : Euclidean n) (s : ℝ) :
      HasDerivAt (fun s : ℝ => f (p+s • x)*ρ x) (fderiv ℝ f (p+s • x) x*ρ x) s := by
    have ha : HasDerivAt (fun s : ℝ => p+s • x) x s := by
      simpa only [zero_add,one_smul] using! (hasDerivAt_const s p).add ((hasDerivAt_id s).smul_const x)
    exact (((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s ha).mul_const (ρ x))
  have hb : Integrable (fun x : Euclidean n => C*‖x‖*ρ x) :=
    ((continuous_const.mul continuous_norm).mul hρ).integrable_of_hasCompactSupport hρs.mul_left
  have hbound (x : Euclidean n) (s : ℝ) :
      ‖fderiv ℝ f (p+s • x) x*ρ x‖ ≤ C*‖x‖*ρ x := by
    rw [norm_mul,Real.norm_eq_abs (ρ x),abs_of_nonneg (euclideanRadialWeight_nonneg n x)]
    exact mul_le_mul_of_nonneg_right
      (((fderiv ℝ f (p+s • x)).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg x))) (euclideanRadialWeight_nonneg n x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := (univ : Set ℝ)) (Filter.univ_mem)
    (Eventually.of_forall fun s => (hF s).aestronglyMeasurable)
    ((hF t).integrable_of_hasCompactSupport hρs.mul_left)
    (hD t).aestronglyMeasurable
    (Eventually.of_forall fun x s _ => hbound x s) hb
    (Eventually.of_forall fun x s _ => hderiv x s)).2

end RegularPointCoordinates

end

end OAI
