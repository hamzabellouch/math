import Mathlib
import OAI.Geometry.WeakHessian.Entropy.DensityConvergence
import OAI.Geometry.WeakHessian.Sobolev.QuadraticGradient
import OAI.Geometry.WeakHessian.Calculus.NormalizedRadial

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile33
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma QuadraticLipschitzBound.centered_bound {o : X} {R : ℝ} (hR : 0 ≤ R)
    {f : X → ℝ} (hf : QuadraticLipschitzBound o R f) (hz : f o = 0) (x : X) :
    |f x| ≤ (dist x o+R)^2 := by
  have H := hf x o
  rw [hz,sub_zero,dist_self] at H
  apply H.trans
  calc
    ((dist x o+0)/2+R)*dist x o ≤ (dist x o+R)*dist x o := by
      nlinarith [sq_nonneg (dist x o)]
    _ ≤ (dist x o+R)*(dist x o+R) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hR) (add_nonneg dist_nonneg hR)
    _ = (dist x o+R)^2 := by ring

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_integrable_of_quadratic_bound {w W f : X → ℝ}
    (hwm : Measurable w) (hW : MemLp (fun x => w x*W x) 2 m)
    (hf : AEStronglyMeasurable f m) (hb : ∀ᵐ x ∂m, |f x| ≤ (W x)^2) :
    Integrable f (squareDensityMeasure m w) ∧ Integrable (fun x => w x^2*f x) m := by
  have hi := hW.integrable_sq
  have hj : Integrable (fun x => w x^2*f x) m := by
    apply hi.mono' (hwm.pow_const 2 |>.aestronglyMeasurable.mul hf)
    filter_upwards [hb] with x hx
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg (w x))]
  exact ⟨(squareDensity_integrable hwm).mpr hj,hj⟩

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_quadratic_pairing_bound {u v W f : X → ℝ}
    (hu : Measurable u) (hv : Measurable v)
    (huW : MemLp (fun x => u x*W x) 2 m) (hvW : MemLp (fun x => v x*W x) 2 m)
    (hf : AEStronglyMeasurable f m) (hb : ∀ᵐ x ∂m, |f x| ≤ (W x)^2) :
    |(∫ x,f x ∂squareDensityMeasure m u)-(∫ x,f x ∂squareDensityMeasure m v)| ≤
      ∫ x,|(u x*W x)^2-(v x*W x)^2| ∂m := by
  have hi := (squareDensity_integrable_of_quadratic_bound hu huW hf hb).2
  have hj := (squareDensity_integrable_of_quadratic_bound hv hvW hf hb).2
  rw [squareDensity_integral hu,squareDensity_integral hv,← integral_sub hi hj,← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (hi.sub hj).norm (huW.integrable_sq.sub hvW.integrable_sq).abs
  filter_upwards [hb] with x hx
  have he : (u x*W x)^2-(v x*W x)^2 = (u x^2-v x^2)*W x^2 := by ring
  simp only [Pi.sub_apply]
  rw [← sub_mul,Real.norm_eq_abs,abs_mul,he,abs_mul,abs_of_nonneg (sq_nonneg (W x))]
  exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)

lemma quadratic_integral_tendsto {o : X} {R : ℝ} (hR : 0 ≤ R)
    {fs : ℕ → X → ℝ} {f w : X → ℝ}
    (hfs : ∀ n, QuadraticLipschitzBound o R (fs n)) (hf : QuadraticLipschitzBound o R f)
    (hz : ∀ n, fs n o = 0) (ht : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (hwm : Measurable w) (hwW : MemLp (fun x => w x*(dist x o+R)) 2 m) :
    Tendsto (fun n => ∫ x,fs n x ∂squareDensityMeasure m w) atTop
      (𝓝 (∫ x,f x ∂squareDensityMeasure m w)) := by
  simp_rw [squareDensity_integral hwm]
  have hmeas : ∀ index, AEStronglyMeasurable (fun point => w point^2*fs index point) m :=
    fun index => (hwm.pow_const 2).aestronglyMeasurable.mul
      ((hfs index).continuous hR).aestronglyMeasurable
  have hbound : ∀ index, ∀ᵐ point ∂m,
      ‖w point^2*fs index point‖ ≤ (w point*(dist point o+R))^2 := by
    intro index
    exact ae_of_all _ fun point => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
      have hweighted := mul_le_mul_of_nonneg_left
        ((hfs index).centered_bound hR (hz index) point) (sq_nonneg (w point))
      nlinarith
  apply tendsto_integral_of_L1 (fun point => w point^2*f point)
    ((hwm.pow_const 2).aestronglyMeasurable.mul (hf.continuous hR).aestronglyMeasurable)
  · exact Eventually.of_forall fun index =>
      hwW.integrable_sq.mono' (hmeas index) (hbound index)
  · simpa only [ofReal_norm] using
      tendsto_lintegral_norm_of_dominated_convergence hmeas hwW.integrable_sq.2 hbound
        (ae_of_all _ fun point => (ht point).const_mul (w point^2))

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma radial_weighted_density_tendsto {w W : X → ℝ}
    (hwW : MemLp (fun x => w x*W x) 2 m) (o : X) (k : ℕ)
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x,|((c n*(w x*radialCutoff o (n+k) x))*W x)^2-(w x*W x)^2| ∂m)
      atTop (𝓝 0) := by
  have H := squareDensity_L1_tendsto
    (fun n => (radial_mul_memLp hwW o (n+k)).const_mul (c n)) hwW
    (normalized_radial_tendsto hwW o k hc)
  convert H using 1
  funext n
  congr 1
  funext x
  congr 1
  ring
end WeakHessian

end
end InlinedFile33

end OAI
