import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.QuadraticCost
import OAI.Geometry.WeakHessian.Calculus.NoncompactCost

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile38
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma quadratic_integral_tendsto_measure {μ : Measure X} {o : X} {R : ℝ} (hR : 0 ≤ R)
    {fs : ℕ → X → ℝ} {f : X → ℝ}
    (hfs : ∀ n, QuadraticLipschitzBound o R (fs n)) (_hf : QuadraticLipschitzBound o R f)
    (hz : ∀ n, fs n o = 0) (ht : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (hW : Integrable (fun x => (dist x o+R)^2) μ) :
    Tendsto (fun n => ∫ x,fs n x ∂μ) atTop (𝓝 (∫ x,f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => (dist x o+R)^2)
  · intro n; exact ((hfs n).continuous hR).aestronglyMeasurable
  · exact hW
  · intro n; exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using (hfs n).centered_bound hR (hz n) x
  · exact ae_of_all _ ht

lemma quadratic_moving_density_integral_tendsto {o : X} {R : ℝ} (hR : 0 ≤ R)
    {fs : ℕ → X → ℝ} {f w : X → ℝ} {us : ℕ → X → ℝ}
    (hfs : ∀ n, QuadraticLipschitzBound o R (fs n)) (hf : QuadraticLipschitzBound o R f)
    (hz : ∀ n, fs n o = 0) (ht : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (hwm : Measurable w) (hum : ∀ n, Measurable (us n))
    (hwW : MemLp (fun x => w x*(dist x o+R)) 2 m)
    (huW : ∀ n, MemLp (fun x => us n x*(dist x o+R)) 2 m)
    (hTV : Tendsto (fun n => ∫ x,|(us n x*(dist x o+R))^2-(w x*(dist x o+R))^2| ∂m) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,fs n x ∂squareDensityMeasure m (us n)) atTop
      (𝓝 (∫ x,f x ∂squareDensityMeasure m w)) := by
  have hD : Tendsto (fun n => (∫ x,fs n x ∂squareDensityMeasure m (us n))-
      (∫ x,fs n x ∂squareDensityMeasure m w)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ hTV
    intro n
    exact squareDensity_quadratic_pairing_bound (hum n) hwm (huW n) hwW
      ((hfs n).continuous hR).aestronglyMeasurable (ae_of_all _ fun x => (hfs n).centered_bound hR (hz n) x)
  have H := hD.add (quadratic_integral_tendsto hR hfs hf hz ht hwm hwW)
  simpa only [zero_add,sub_add_cancel] using H

variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
lemma limit_quadratic_transport_support
    {us : ℕ → X → ℝ} {w : X → ℝ} (hum : ∀ n, Measurable (us n)) (hwm : Measurable w)
    (o : X) (R : ℝ≥0)
    (huW : ∀ n, MemLp (fun x => us n x*(dist x o+R)) 2 m)
    (hwW : MemLp (fun x => w x*(dist x o+R)) 2 m)
    (hTV : Tendsto (fun n => ∫ x,|(us n x*(dist x o+R))^2-(w x*(dist x o+R))^2| ∂m) atTop (𝓝 0))
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (ps : ℕ → ProbabilityMeasure (Curve X))
    (h0 : ∀ n, interpolation (ps n:Measure (Curve X)) timeZero = squareDensityMeasure m (us n))
    (h1 : ∀ n, interpolation (ps n:Measure (Curve X)) timeOne = (ν:Measure X))
    (φs ψs : ℕ → X → ℝ) (φ : X → ℝ)
    (hφs : ∀ n, QuadraticLipschitzBound o R (φs n)) (hφ : QuadraticLipschitzBound o R φ)
    (hz : ∀ n, φs n o = 0) (ht : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x)))
    (hψ : ∀ n, Continuous (ψs n)) (hiψ : ∀ n, Integrable (ψs n) (ν:Measure X))
    {S : Set X} (hS : MeasurableSet S) (hs : ∀ᵐ y ∂(ν:Measure X), y ∈ S)
    (hd : ∀ n x y, y ∈ S → φs n x+ψs n y ≤ dist x y^2/2)
    (hc : ∀ n, ∀ᵐ γ ∂(ps n:Measure (Curve X)), φs n (γ timeZero)+ψs n (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    {E : ℝ} (hE : Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 E))
    (ξ : ProbabilityMeasure X) (hξW : Integrable (fun x => (dist x o+R)^2) (ξ:Measure X))
    {q : Measure (X×X)} (hq : IsCoupling q ξ ν) (hqt : QuadraticTransportCost q ≠ ∞) :
    E-(QuadraticTransportCost q).toReal ≤
      2*((∫ x,φ x ∂(μ:Measure X))-(∫ x,φ x ∂(ξ:Measure X))) := by
  have ip (n : ℕ) := (squareDensity_integrable_of_quadratic_bound (hum n) (huW n)
    ((hφs n).continuous R.coe_nonneg).aestronglyMeasurable (ae_of_all _ fun x => (hφs n).centered_bound R.coe_nonneg (hz n) x)).1
  have iq (n : ℕ) : Integrable (φs n) (ξ:Measure X) :=
    hξW.mono' ((hφs n).continuous R.coe_nonneg).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using (hφs n).centered_bound R.coe_nonneg (hz n) x)
  have hv := quadratic_moving_density_integral_tendsto R.coe_nonneg hφs hφ hz ht hwm hum hwW huW hTV
  have hx := quadratic_integral_tendsto_measure R.coe_nonneg hφs hφ hz ht hξW
  have heq : (QuadraticTransportCost q).toReal = ∫ p : X×X,dist p.1 p.2^2 ∂q := by
    rw [quadraticTransportCost_eq_integral hqt,ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  rw [heq,hμ]
  apply le_of_tendsto_of_tendsto' (hE.sub_const _) ((hv.sub hx).const_mul 2)
  intro n
  simpa only [h0 n] using planEnergy_le_coupling_of_restricted_contact hqt ξ ν hq (h1 n)
    ((hφs n).continuous R.coe_nonneg) (hψ n) (h0 n ▸ ip n) (iq n) (hiψ n) hS hs (hd n) (hc n)
end WeakHessian

end
end InlinedFile38

end OAI
