import OAI.Geometry.RCD.Transport.RenyiMidpointAbsoluteContinuity
import OAI.Geometry.RCD.Transport.RenyiMeasureReplacement

namespace OAI

/-! # Bounded density of the actual Rényi-maximizing midpoint

The sharp midpoint capacity controls every Rényi maximizer.
The proof first removes singular mass and then uses strict improvement
under a bounded replacement of a density superlevel set.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.renyi_midpoint_compressed
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₀ • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmax : RenyiMaximizingPlan ((hausdorff n X).restrict (closedBall p (3*R)))
      ν₀ ν₁ π midpointTime q) :
    π.map (fun γ => γ midpointTime) ≤ midpointCapacity K n (2*R) C₀ • hausdorff n X := by
  let : SeparableSpace X := hX.separable
  let μ := (hausdorff n X).restrict (closedBall p (3*R))
  let : IsFiniteMeasure μ := ⟨by
    simpa [μ] using hX.finiteOnBounded (closedBall p (3*R)) isBounded_closedBall⟩
  let ν := π.map (fun γ => γ midpointTime)
  let C := midpointCapacity K n (2*R) C₀
  have hCtop : C ≠ ∞ := midpointCapacity_ne_top K n (2*R) hC₀
  have hC0 : C ≠ 0 := (midpointCapacity_pos K n (2*R) (probability_capacity_ne_zero _ _ h0)).ne'
  have hCreal : 0 < C.toReal := ENNReal.toReal_pos hC0 hCtop
  have hCe : ENNReal.ofReal C.toReal = C := ENNReal.ofReal_toReal hCtop
  have hac : ν ≪ μ := hX.renyi_midpoint_absolutelyContinuous K n hn ν₀ ν₁ hC₀ h0 h1
    hm0 hm1 p hR hs0 hs1 π hg hp hq0 hq1 hmax
  have hsupport : ∀ᵐ x ∂ν, x ∈ closedBall p (3*R) := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ π hg hp p hR hs0 hs1).mono
      (fun γ hγ => hγ.2 midpointTime)
  by_contra hbad
  have hbad' : ¬ν ≤ ENNReal.ofReal C.toReal • μ := by
    rw [hCe]
    exact fun h => hbad ((compression_iff_localized _ _ hsupport C).mpr h)
  let B := {x | C.toReal < (ν.rnDeriv μ x).toReal}
  have hB : MeasurableSet B := measurableSet_lt measurable_const (ν.measurable_rnDeriv μ).ennreal_toReal
  have hm : ν B ≠ 0 := superlevel_mass_ne_zero_of_not_compressed μ ν hac hCreal hbad'
  obtain ⟨σ,hσ,hgσ,hpσ,hmσ,hcapσ⟩ := hX.compressed_replacement_subplan K n hn
    ν₀ ν₁ hC₀ h0 h1 hm0 hm1 p hR hs0 hs1 π hg hp B hB hm
  let := hσ
  let η := σ.map (fun γ => γ midpointTime)
  obtain ⟨a,ha0,ha1,hgain⟩ := exists_measure_renyi_increase μ ν η hac hq0 hq1 hCreal
    (by simpa only [hCe] using hcapσ) hmσ hbad'
  let κ := π.restrict ((fun γ => γ midpointTime) ⁻¹' B)
  have hκ : κ ≤ π := Measure.restrict_le_self
  have haE : ENNReal.ofReal a ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal ha1.le
  have hsub : ENNReal.ofReal a • κ ≤ π := by
    calc
      _ ≤ (1:ℝ≥0∞) • κ := fun S => by
        simpa only [Measure.smul_apply,smul_eq_mul] using mul_le_mul_left haE (κ S)
      _ = κ := one_smul _ _
      _ ≤ π := hκ
  have hs : IsOptimalCoupling ((ENNReal.ofReal a • κ).map (fun γ => γ 0))
      ((ENNReal.ofReal a • κ).map (fun γ => γ 1))
      ((ENNReal.ofReal a • σ).map (fun γ => (γ 0,γ 1))) := by
    simpa only [Measure.map_smul _ (measurable_path_eval 0).aemeasurable,
      Measure.map_smul _ (measurable_path_eval 1).aemeasurable,
      Measure.map_smul _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable]
      using hpσ.smul (ENNReal.ofReal_pos.mpr ha0).ne' ENNReal.ofReal_ne_top
  have hgs : ∀ᵐ γ ∂(ENNReal.ofReal a • σ), IsGeodesic γ :=
    hgσ.filter_mono Measure.smul_absolutelyContinuous.ae_le
  obtain ⟨hprob,hgeo,hopt⟩ := optimalPlan_replace_subplan hp hg hsub hs hgs
  have hle := hmax _ hprob hgeo hopt
  have hκmid : κ.map (fun γ => γ midpointTime) = ν.restrict B :=
    (Measure.restrict_map (measurable_path_eval midpointTime) hB).symm
  rw [Measure.map_add _ _ (measurable_path_eval midpointTime),
    map_sub_of_le π (ENNReal.ofReal a • κ) hsub _ (measurable_path_eval midpointTime),
    Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable,
    Measure.map_smul _ (measurable_path_eval midpointTime).aemeasurable,hκmid] at hle
  exact (not_lt_of_ge hle) hgain

theorem NoncollapsedRCD.exists_compressed_renyi_maximizing_midpoint
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • hausdorff n X) (h1 : ν₁ ≤ C₀ • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ π : Measure C(Time,X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧ IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))) ∧
      π.map (fun γ => γ midpointTime) ≤ midpointCapacity K n (2*R) C₀ • hausdorff n X ∧
      RenyiMaximizingPlan ((hausdorff n X).restrict (closedBall p (3*R))) ν₀ ν₁ π midpointTime q := by
  obtain ⟨π,hπ,hg,hp,hmax⟩ := hX.exists_renyi_maximizing_midpoint K n hn ν₀ ν₁ hC₀
    h0 h1 hm0 hm1 p hR hs0 hs1 hq0 hq1
  let := hπ
  exact ⟨π,hπ,hg,hp,hX.renyi_midpoint_compressed K n hn ν₀ ν₁ hC₀ h0 h1 hm0 hm1
    p hR hs0 hs1 π hg hp hq0 hq1 hmax,hmax⟩

end RegularPointCoordinates

end

end OAI
