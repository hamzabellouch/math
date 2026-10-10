import OAI.Dynamics.StandardMap.SweepSlice

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma measurable_liftProjection : Measurable liftProjection :=
  (((AddCircle.continuous_mk' (1:ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_snd)).measurable
lemma bounded_lift_event (A : Set Torus) (V : Set (ℝ × ℝ)) (hA : MeasurableSet A)
    (hV : MeasurableSet V) (hb : V ⊆ Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2)
    (hp : ∀ z ∈ V, liftProjection z ∈ A) : volume V ≤ 16*area A := by
  have hh := bounded_lift_integral (A.indicator (fun _ => (1:ℝ≥0∞)))
    (measurable_const.indicator hA) V hb
  have he : (∫⁻ z in V, A.indicator (fun _ => (1:ℝ≥0∞)) (liftProjection z))=volume V := by
    calc
      _ = ∫⁻ z in V, (1:ℝ≥0∞) := setLIntegral_congr_fun hV (fun z hz => indicator_of_mem (hp z hz) _)
      _ = _ := by simp
  rw [he,lintegral_indicator hA] at hh
  simpa using hh
lemma scaled_product_slice_bound (E I : Set ℝ) (T : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ≥0∞)
    (d K : ℝ≥0∞) (hd : d ≠ ∞) (hE : MeasurableSet E) (hI : MeasurableSet I) (hT : MeasurableSet T)
    (hsub : T ⊆ E ×ˢ I)
    (hslice : ∀ x ∈ E, d*(∫⁻ y in I, T.indicator f (x,y)) ≤ K) :
    d*(∫⁻ z in T, f z) ≤ K*volume E := by
  have hi (z : ℝ × ℝ) : T.indicator (fun w => d*f w) z=d*T.indicator f z := by
    by_cases hz : z ∈ T <;> simp [hz]
  have hh := product_slice_bound E I T (fun z => d*f z) K hE hI hT hsub (by
    intro x hx
    simpa only [hi,lintegral_const_mul' _ _ hd] using hslice x hx)
  simpa only [lintegral_const_mul' _ _ hd] using hh
end StandardMapEntropy

end OAI
