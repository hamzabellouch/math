import OAI.Geometry.RCD.Transport.RenyiLocalization

namespace OAI

/-! # A compressed midpoint with the original finite-CD lower value

The entropy-maximizing midpoint dominates the original CD midpoint. The
distortion integral still uses that original CD witness; no equality of
the two endpoint couplings is asserted.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [BorelSpace X] in
theorem RenyiMaximizingPlan.renyiIntegral_le (μ : Measure X) [SigmaFinite μ]
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    {ν₀ ν₁ : Measure X} {π κ : Measure C(Time,X)}
    [IsProbabilityMeasure π] [IsProbabilityMeasure κ] {t : Time} {N : ℝ} (hN : 1 < N)
    (hmax : RenyiMaximizingPlan (μ.restrict B) ν₀ ν₁ π t (1-1/N))
    (hgκ : ∀ᵐ γ ∂κ, IsGeodesic γ)
    (hpκ : IsOptimalCoupling ν₀ ν₁ (κ.map (fun γ => (γ 0,γ 1))))
    (hsπ : ∀ᵐ x ∂π.map (fun γ => γ t), x∈B)
    (hsκ : ∀ᵐ x ∂κ.map (fun γ => γ t), x∈B) :
    renyiIntegral μ (κ.map (fun γ => γ t)) N ≤ renyiIntegral μ (π.map (fun γ => γ t)) N := by
  have hN0 : 0 < N := by linarith
  have hq0 : 0 < 1-1/N := sub_pos.mpr ((div_lt_one hN0).mpr hN)
  have hq1 : 1-1/N ≤ 1 := by have := one_div_pos.mpr hN0; linarith
  have hi (η : Measure X) [IsProbabilityMeasure η] :
      Integrable (fun x => (η.rnDeriv (μ.restrict B) x).toReal^(1-1/N)) (μ.restrict B) :=
    integrable_density_power (μ.restrict B) _ (η.measurable_rnDeriv (μ.restrict B)).ennreal_toReal
      Measure.integrable_toReal_rnDeriv (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hq0.le hq1
  rw [renyiIntegral_localized μ _ hB hsκ hN,renyiIntegral_localized μ _ hB hsπ hN]
  exact (rnDeriv_power_lintegral_eq_of_integrable (μ.restrict B) _ hq0.le (hi _)).trans_le
    ((ENNReal.ofReal_le_ofReal (hmax κ inferInstance hgκ hpκ)).trans_eq
      (rnDeriv_power_lintegral_eq_of_integrable (μ.restrict B) _ hq0.le (hi _)).symm)

theorem NoncollapsedRCD.exists_compressed_finite_renyi_midpoint
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    {N : ℝ} (hN : (n:ℝ) ≤ N) :
    ∃ π : Measure C(Time,X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧ IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))) ∧
      π.map (fun γ => γ midpointTime) ≤ midpointCapacity K n (2*R) C • hausdorff n X ∧
      ∃ τ : Measure C(Time,X), IsProbabilityMeasure τ ∧
        (∀ᵐ γ ∂τ, IsGeodesic γ) ∧ IsOptimalCoupling ν₀ ν₁ (τ.map (fun γ => (γ 0,γ 1))) ∧
        (∫⁻ γ, tau K N (1/2) (dist (γ 0) (γ 1))*(ν₀.rnDeriv (hausdorff n X) (γ 0))^(-(1/N))+
          tau K N (1/2) (dist (γ 0) (γ 1))*(ν₁.rnDeriv (hausdorff n X) (γ 1))^(-(1/N)) ∂τ) ≤
          renyiIntegral (hausdorff n X) (π.map (fun γ => γ midpointTime)) N := by
  let : SeparableSpace X := hX.separable
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hN1 : 1 < N := by linarith
  have hq0 : 0 < 1-1/N := sub_pos.mpr ((div_lt_one (by linarith : 0 < N)).mpr hN1)
  have hq1 : 1-1/N < 1 := by have := one_div_pos.mpr (by linarith : 0 < N); linarith
  obtain ⟨π,hπ,hgπ,hpπ,hcap,hmax⟩ := hX.exists_compressed_renyi_maximizing_midpoint K n hn
    ν₀ ν₁ hC h0 h1 hm0 hm1 p hR hs0 hs1 hq0 hq1
  let := hπ
  obtain ⟨τ,hτ,hgτ,hpτ,hcd⟩ := hX.cd ν₀ ν₁ inferInstance inferInstance
    (Measure.absolutelyContinuous_of_le_smul h0) (Measure.absolutelyContinuous_of_le_smul h1) hm0 hm1
  let := hτ
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let B := closedBall p (3*R)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ,B] using hX.finiteOnBounded B isBounded_closedBall⟩
  have hsupport (σ : Measure C(Time,X)) (hgσ : ∀ᵐ γ ∂σ, IsGeodesic γ)
      (hpσ : IsOptimalCoupling ν₀ ν₁ (σ.map (fun γ => (γ 0,γ 1)))) :
      ∀ᵐ x ∂σ.map (fun γ => γ midpointTime), x∈B := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ σ hgσ hpσ p hR hs0 hs1).mono
      (fun γ hγ => hγ.2 midpointTime)
  refine ⟨π,hπ,hgπ,hpπ,hcap,τ,hτ,hgτ,hpτ,?_⟩
  have hl := hmax.renyiIntegral_le μ measurableSet_closedBall hN1 hgτ hpτ
    (hsupport π hgπ hpπ) (hsupport τ hgτ hpτ)
  have hc := (hcd N hN midpointTime).trans hl
  convert hc using 1; norm_num [midpointTime]

end RegularPointCoordinates

end

end OAI
