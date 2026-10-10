import OAI.Geometry.RCD.Heat.BoundedHeatIntegral

namespace OAI

/-! # Pointwise semigroup law for the constructed heat measures -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology CompactlySupported

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem HasBoundedAmplitude.heatAt {f : Lp ℝ 2 (hausdorff n X)}
    (hf : HasBoundedAmplitude f) (t : ℝ) :
    HasBoundedAmplitude (heatAt (hausdorff n X) hX.quadratic t f) :=
  ⟨hf.choose, heatAt_abs_le_const _ _ t hf.choose f hf.choose_spec⟩

namespace NoncollapsedRCD

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
/-- Uniqueness of continuous representatives upgrades the L² semigroup
identity to equality at every point. -/
theorem boundedHeat_semigroup (f : Lp ℝ 2 (hausdorff n X))
    (hf : HasBoundedAmplitude f) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    hX.boundedHeat hn p (heatAt (hausdorff n X) hX.quadratic t f)
      (hf.heatAt hX t) s hs =
      hX.boundedHeat hn p f hf (s + t) (add_pos hs ht) := by
  apply hX.boundedHeat_unique hn p
  · exact hX.boundedHeat_continuous hn p f hf (s + t) (add_pos hs ht)
  · rw [← mul_apply_eq_comp, ← heatAt_add _ _ s t hs.le ht.le]
    exact hX.boundedHeat_represents hn p f hf (s + t) (add_pos hs ht)

/-- Iterated integration of bounded L² data agrees with time addition,
for every starting point of the constructed probability family. -/
theorem heatRadonMeasure_integral_semigroup (f : Lp ℝ 2 (hausdorff n X))
    (C : ℝ≥0) (hf : ∀ᵐ y ∂hausdorff n X, |f y| ≤ C)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x : X) :
    (∫ y, (∫ z, f z ∂hX.heatRadonMeasure hn p t ht y)
      ∂hX.heatRadonMeasure hn p s hs x) =
      ∫ z, f z ∂hX.heatRadonMeasure hn p (s + t) (add_pos hs ht) x := by
  simp_rw [hX.heatRadonMeasure_integral_bounded hn p t ht _ f C hf]
  have he := (hX.heatRadonMeasure_absolutelyContinuous hn p s hs x).ae_le
    (hX.boundedHeat_represents hn p f ⟨C, hf⟩ t ht)
  rw [← integral_congr_ae he]
  rw [hX.heatRadonMeasure_integral_bounded hn p s hs x _ C
    (heatAt_abs_le_const _ _ t C f hf)]
  rw [hX.boundedHeat_semigroup hn p f ⟨C, hf⟩ s t hs ht]
  exact (hX.heatRadonMeasure_integral_bounded hn p (s + t) (add_pos hs ht) x f C hf).symm

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
