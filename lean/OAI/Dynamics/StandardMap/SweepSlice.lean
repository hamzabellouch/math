import OAI.Dynamics.StandardMap.EndpointTransport

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma sweep_slice_bound (I D : Set ℝ) (f : (ℝ × ℝ) → (ℝ × ℝ))
    (J : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (w : ℝ → ℝ≥0∞) (g : Torus → ℝ≥0∞) (c : ℝ) (δ : ℝ≥0∞)
    (hI : MeasurableSet I) (hD : MeasurableSet D) (hw : Measurable w) (hg : Measurable g)
    (hJ : ∀ z ∈ I ×ˢ D, HasFDerivWithinAt f (J z) (I ×ˢ D) z)
    (hinj : InjOn f (I ×ˢ D))
    (hlo : ∀ z ∈ I ×ˢ D, c ≤ |(J z).det|)
    (himage : f '' (I ×ˢ D) ⊆ Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2)
    (hobs : ∀ z ∈ I ×ˢ D, w z.2 ≤ g (liftProjection (f z))+δ) :
    (ENNReal.ofReal c*volume I)*(∫⁻ y in D, w y) ≤
      16*(∫⁻ z, g z ∂area)+(ENNReal.ofReal c*volume I)*δ*volume D := by
  have hbase := weighted_sweep_bound volume (I ×ˢ D) f J c (g ∘ liftProjection)
    (fun z => w z.2) δ (hI.prod hD) hJ hinj hlo hobs
  have he : (∫⁻ z in I ×ˢ D, w z.2) = volume I*(∫⁻ y in D, w y) := by
    change (∫⁻ z, w z.2 ∂(volume.prod volume).restrict (I ×ˢ D)) = _
    have hw' : Measurable (fun z : ℝ × ℝ => w z.2) := hw.comp measurable_snd
    rw [← Measure.prod_restrict,lintegral_prod _ hw'.aemeasurable]
    simp [mul_comm]
  rw [he] at hbase
  have hm : volume (I ×ˢ D) = volume I*volume D := Measure.prod_prod _ _
  rw [hm] at hbase
  calc
    _ = ENNReal.ofReal c*(volume I*(∫⁻ y in D, w y)) := by ring
    _ ≤ (∫⁻ z in f '' (I ×ˢ D), g (liftProjection z))+ENNReal.ofReal c*δ*(volume I*volume D) := hbase
    _ ≤ 16*(∫⁻ z, g z ∂area)+(ENNReal.ofReal c*volume I)*δ*volume D := by
      have h := bounded_lift_integral g hg (f '' (I ×ˢ D)) himage
      calc
        _ ≤ 16*(∫⁻ z, g z ∂area)+ENNReal.ofReal c*δ*(volume I*volume D) := add_le_add h le_rfl
        _ = _ := by ring

end StandardMapEntropy

end OAI
