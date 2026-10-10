import OAI.Geometry.RCD.Heat.BoundedHeatMixedGram
import OAI.Geometry.RCD.Heat.BoundedHeatSobolevData
import OAI.Geometry.RCD.Harmonic.QuadraticUniformBounds

namespace OAI

/-! # Bounded mixed heat Grams and compact positive ranges -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  [(hausdorff n X).Regular] [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n) (p : X)

include hn p in
theorem bounded_heat_mixed_gram_bound (f g : Lp ℝ 2 (hausdorff n X)) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A)
    (hg : ∀ᵐ x ∂hausdorff n X, |g x| ≤ B) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ∃ (G : SobolevSpace (hausdorff n X) hX.quadratic) (C : ℝ≥0),
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic
          (heatSobolev (hausdorff n X) hX.quadratic s hs f)
          (heatSobolev (hausdorff n X) hX.quadratic t ht g)) ∧
      ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic G x| ≤ C := by
  obtain ⟨G,hG⟩ := hX.bounded_heat_mixed_gram hn p f g A B hf hg hs ht
  obtain ⟨-,L,hL⟩ := hX.bounded_heat_sobolev_data hn p f A hf hs
  obtain ⟨-,M,hM⟩ := hX.bounded_heat_sobolev_data hn p g B hg ht
  have hb := gamma_abs_le_of_bounds (hausdorff n X) hX.quadratic
    (Ω := univ) _ _ L.coe_nonneg M.coe_nonneg
    (by simpa only [Measure.restrict_univ] using hL)
    (by simpa only [Measure.restrict_univ] using hM)
  simp only [Measure.restrict_univ] at hb
  refine ⟨G,L*M,hG,?_⟩
  filter_upwards [hG,hb] with x hx hb
  exact hx ▸ hb

include hn p in
theorem bounded_heat_positive_range (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {s : ℝ} (hs : 0 < s)
    {Ω : Set X} (hΩ : IsCompact Ω)
    (hpos : ∀ x ∈ Ω, 0 < kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s f x) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ᵐ x ∂(hausdorff n X).restrict Ω,
        SobolevSpace.toLp (hausdorff n X) hX.quadratic
          (heatSobolev (hausdorff n X) hX.quadratic s hs f) x ∈ Icc a b := by
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨hLip,hBound⟩ := hX.kernelHeat_bounded_regularity hn p hk f A hf s hs
  obtain ⟨a,ha,haH⟩ := hΩ.exists_forall_le' hLip.continuous.continuousOn hpos
  refine ⟨a,max a A,ha,le_max_left _ _,?_⟩
  filter_upwards [ae_restrict_of_ae (kernelHeat_represents_L2 (hausdorff n X)
    hX.quadratic hk hs f),ae_restrict_mem hΩ.measurableSet] with x hx hmem
  simpa only [heatSobolev_toLp,← hx] using
    show kernelHeat (hausdorff n X) hX.quadratic hk s f x ∈ Icc a (max a A) from
      ⟨haH x hmem,(le_abs_self _).trans ((hBound x).trans (le_max_right _ _))⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
