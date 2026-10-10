import Mathlib
import OAI.Analysis.RCDHeat.KantorovichRadius
import OAI.Analysis.RCDHeat.WeightedGradientConvex

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: CompactTransportVariation, WeightedPairLinear, EntropyKantorovich, OptimalSubcoupling, OptimalSubplan. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

 theorem compact_optimal_plan_signed_variation [CompactSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (hspace : IsGeodesicSpace X) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) :
    ∃ (u : SobolevSpace μ hQ) (φ ψ : X → ℝ) (L : ℝ≥0),
      LipschitzWith L φ ∧ LipschitzWith L ψ ∧
      (φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2) ∧
      (∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) = dist (γ 0) (γ 1)) ∧
      ∀ g : SobolevSpace μ hQ,
        Tendsto (planInitialSecant π (SobolevSpace.toLp μ hQ g)) (𝓝[>] (0:ℝ))
          (𝓝 (-weightedGradientPair μ hQ ν₀ u g)) := by
  obtain ⟨u,φ,ψ,L,hφ,hψ,hu,had,hc,hid⟩ :=
    compact_optimal_plan_gradient_identity μ hQ hspace ν₀ ν₁ π hgeo hp hC hcomp
  have hm := (measurable_path_eval (X := X) 0).prodMk (measurable_path_eval 1)
  have hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π := by
    have hd := ((continuous_fst.dist continuous_snd : Continuous (fun xy : X×X => dist xy.1 xy.2)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (p := 2) (μ := π.map (fun γ => (γ 0,γ 1))))
    exact hd.comp_of_map hm.aemeasurable
  refine ⟨u,φ,ψ,L,hφ,hψ,hu,had,hc,hid,fun g => ?_⟩
  have hh := kantorovich_signed_first_variation μ hQ π hgeo hC hcomp hD u g hu had hc
    (hid.mono fun _ he => he.le)
  rwa [(optimalPlan_endpoints ν₀ ν₁ π hp).1] at hh
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

 

 theorem convex_directional_derivative_add {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : E → ℝ) (hc : ConvexOn ℝ univ F) (f : E) (d : E → ℝ)
    (hd : ∀ g, HasDerivAt (fun t : ℝ => F (f+t • g)) (d g) 0) (g h : E) :
    d (g+h) = d g+d h := by
  have htwice (v : E) : HasDerivAt (fun t : ℝ => F (f+(2*t) • v)) (2*d v) 0 := by
    have hh := (hd v).comp_of_eq 0 ((hasDerivAt_id (0:ℝ)).const_mul 2) (by simp)
    simpa [Function.comp_def,mul_comm] using hh
  let H := fun t : ℝ => (1/2:ℝ)*F (f+(2*t) • g)+(1/2:ℝ)*F (f+(2*t) • h)-F (f+t • (g+h))
  have hH : ∀ t, 0 ≤ H t := by
    intro t
    have hh := hc.2 (mem_univ (f+(2*t) • g)) (mem_univ (f+(2*t) • h))
      (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
      (show (1/2:ℝ)+1/2=1 by norm_num)
    have he : (1/2:ℝ) • (f+(2*t) • g)+(1/2:ℝ) • (f+(2*t) • h) = f+t • (g+h) := by
      module
    rw [he] at hh
    exact sub_nonneg.mpr hh
  have hmin : IsLocalMin H (0:ℝ) := by
    apply Filter.Eventually.of_forall
    intro t
    have hzero : H 0 = 0 := by simp only [H,mul_zero,zero_smul,add_zero]; ring
    rw [hzero]
    exact hH t
  have hder : HasDerivAt H ((1/2:ℝ)*(2*d g)+(1/2:ℝ)*(2*d h)-d (g+h)) 0 :=
    (((htwice g).const_mul (1/2)).add ((htwice h).const_mul (1/2))).sub (hd (g+h))
  have hz := hmin.hasDerivAt_eq_zero hder
  linarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem weightedGradientPair_add_right {ν : Measure X} [IsFiniteMeasure ν]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • μ) (f g h : SobolevSpace μ hQ) :
    weightedGradientPair μ hQ ν f (g+h) =
      weightedGradientPair μ hQ ν f g+weightedGradientPair μ hQ ν f h := by
  have hh := convex_directional_derivative_add (weightedGradientSquare μ hQ ν)
    (weightedGradientSquare_convex μ hQ hC hν) f
    (fun v => 2*weightedGradientPair μ hQ ν f v)
    (weightedGradientSquare_hasDerivAt_zero μ hQ hC hν f) g h
  linarith

 theorem weightedGradientPair_smul_right {ν : Measure X} [IsFiniteMeasure ν]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • μ) (f g : SobolevSpace μ hQ) (a : ℝ) :
    weightedGradientPair μ hQ ν f (a • g) = a*weightedGradientPair μ hQ ν f g := by
  have hd := (weightedGradientSquare_hasDerivAt_zero μ hQ hC hν f g).comp_of_eq 0
    ((hasDerivAt_id (0:ℝ)).mul_const a) (by simp)
  have he : (fun t : ℝ => weightedGradientSquare μ hQ ν (f+(t*a) • g)) =
      (fun t : ℝ => weightedGradientSquare μ hQ ν (f+t • (a • g))) := by
    simp only [mul_smul]
  change HasDerivAt (fun t : ℝ => weightedGradientSquare μ hQ ν (f+(t*a) • g)) _ _ at hd
  rw [he] at hd
  have hh := hd.deriv
  have hh' := (weightedGradientSquare_hasDerivAt_zero μ hQ hC hν f (a • g)).deriv
  linarith

omit [ProperSpace X] in
 

 theorem weightedGradientPair_reference (f g : SobolevSpace μ hQ) :
    weightedGradientPair μ hQ μ f g = energyForm μ hQ f g := by
  have he (t : ℝ) : weightedGradientSquare μ hQ μ (f+t • g) =
      2*SobolevSpace.energy μ hQ f+2*t*energyForm μ hQ f g+
        2*t^2*SobolevSpace.energy μ hQ g := by
    rw [weightedGradientSquare_self]
    have hh := form_sub_smul μ hQ f g (-t)
    simp only [neg_smul,sub_neg_eq_add,neg_sq] at hh
    rw [hh]
    ring
  have hd := (((hasDerivAt_const (0:ℝ) (2*SobolevSpace.energy μ hQ f)).add
      (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const (energyForm μ hQ f g))).add
      ((((hasDerivAt_id (0:ℝ)).pow 2).const_mul 2).mul_const (SobolevSpace.energy μ hQ g)))
  have hder : deriv (fun t : ℝ => 2*SobolevSpace.energy μ hQ f+
      2*t*energyForm μ hQ f g+2*t^2*SobolevSpace.energy μ hQ g) 0 =
      2*energyForm μ hQ f g := by
    simpa using! hd.deriv
  unfold weightedGradientPair
  simp_rw [he]
  rw [hder]
  ring
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 theorem planInitialSecant_congr_ae (μ : Measure X) (π : Measure C(Time,X))
    (hac : ∀ s : Time, π.map (fun γ => γ s) ≪ μ)
    {f g : X → ℝ} (hfg : f =ᵐ[μ] g) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    planInitialSecant π f t = planInitialSecant π g t := by
  have hp (s : Time) : ∀ᵐ γ ∂π, f (γ s) = g (γ s) :=
    ae_of_ae_map (measurable_path_eval s).aemeasurable ((hac s).ae_eq hfg)
  dsimp only [planInitialSecant]
  congr 1
  apply integral_congr_ae
  filter_upwards [hp (⟨t,ht⟩:Time),hp 0] with γ ht' h0
  rw [geodesicExtension_eq γ (⟨t,ht⟩:Time),ht',h0]

 

 theorem entropy_plan_signed_derivative_le (μ : Measure X) [SigmaFinite μ]
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀]
    (h0 : ν₀ ≪ μ) (hpos : ∀ᵐ x ∂μ, 0 < (ν₀.rnDeriv μ x).toReal)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (φ : X → ℝ) {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (hrep : φ =ᵐ[μ] fun x => Real.log (ν₀.rnDeriv μ x).toReal)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hmap0 : π.map (fun γ => γ 0) = ν₀)
    (hD : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)) π)
    (K : ℝ) (hac : ∀ t : Time, π.map (fun γ => γ t) ≪ μ)
    (hconv : ∀ t : Time,
      Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal *
        Real.log ((π.map (fun γ => γ t)).rnDeriv μ x).toReal) μ ∧
      boltzmannEntropy μ (π.map (fun γ => γ t)) ≤
        (1-(t:ℝ))*boltzmannEntropy μ ν₀+(t:ℝ)*boltzmannEntropy μ ν₁+
        ((-K)*(t:ℝ)*(1-(t:ℝ))/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂π))
    {d : ℝ} (hd : Tendsto (planInitialSecant π φ) (𝓝[>] (0:ℝ)) (𝓝 d)) :
    d ≤ boltzmannEntropy μ ν₁-boltzmannEntropy μ ν₀-
      (K/2)*(∫γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂π) := by
  have hlim : Tendsto (fun t : ℝ => boltzmannEntropy μ ν₁-boltzmannEntropy μ ν₀-
      (K*(1-t)/2)*(∫γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂π))
      (𝓝[>] (0:ℝ)) (𝓝 (boltzmannEntropy μ ν₁-boltzmannEntropy μ ν₀-
        (K/2)*(∫γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂π))) := by
    have hc' : Continuous (fun t : ℝ => boltzmannEntropy μ ν₁-boltzmannEntropy μ ν₀-
        (K*(1-t)/2)*(∫γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂π)) := by fun_prop
    simpa using (hc'.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hd hlim
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
    (gt_mem_nhds (show (0:ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall,self_mem_nhdsWithin] with t ht1 ht0
  change 0 < t at ht0
  let s : Time := ⟨t,ht0.le,ht1.le⟩
  have hh := entropy_plan_signed_secant μ ν₀ ν₁ h0 hpos he0 φ hφ hrep π hg
    hmap0 hD K s ht0 (hac s) (hconv s).1 (hconv s).2
  rw [integral_div] at hh
  have hge (γ : C(Time,X)) : geodesicExtension γ t = γ s := geodesicExtension_eq γ s
  dsimp only [planInitialSecant]
  simp_rw [hge]
  exact hh

 

 theorem compact_entropy_plan_kantorovich_bound [CompactSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (hspace : IsGeodesicSpace X) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hpos : ∀ᵐ x ∂μ, 0 < (ν₀.rnDeriv μ x).toReal)
    (he0 : Integrable (fun x => (ν₀.rnDeriv μ x).toReal*Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (ℓ : X → ℝ) {L : ℝ≥0} (hℓ : LipschitzWith L ℓ)
    (hlog : ℓ =ᵐ[μ] fun x => Real.log (ν₀.rnDeriv μ x).toReal)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (K : ℝ)
    (hconv : ∀ t : Time,
      Integrable (fun x => ((π.map (fun γ => γ t)).rnDeriv μ x).toReal *
        Real.log ((π.map (fun γ => γ t)).rnDeriv μ x).toReal) μ ∧
      boltzmannEntropy μ (π.map (fun γ => γ t)) ≤
        (1-(t:ℝ))*boltzmannEntropy μ ν₀+(t:ℝ)*boltzmannEntropy μ ν₁+
        ((-K)*(t:ℝ)*(1-(t:ℝ))/2)*(∫γ, dist (γ 0) (γ 1)^2 ∂π)) :
    ∃ (u : SobolevSpace μ hQ) (φ ψ : X → ℝ) (M : ℝ≥0),
      LipschitzWith M φ ∧ LipschitzWith M ψ ∧
      (φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2) ∧
      -weightedGradientPair μ hQ ν₀ u
        (SobolevSpace.ofLipschitzCompact μ hQ hℓ (HasCompactSupport.of_compactSpace _)) ≤
        boltzmannEntropy μ ν₁-boltzmannEntropy μ ν₀-
          (K/2)*(∫γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂π) := by
  obtain ⟨u,φ,ψ,M,hφ,hψ,hu,had,hc,_,hvar⟩ :=
    compact_optimal_plan_signed_variation μ hQ hspace ν₀ ν₁ π hgeo hp hC hcomp
  refine ⟨u,φ,ψ,M,hφ,hψ,hu,had,hc,?_⟩
  let g := SobolevSpace.ofLipschitzCompact μ hQ hℓ (HasCompactSupport.of_compactSpace _)
  have hrep : SobolevSpace.toLp μ hQ g =ᵐ[μ] ℓ :=
    SobolevSpace.ofLipschitzCompact_coe μ hQ hℓ (HasCompactSupport.of_compactSpace _)
  have hac (s : Time) : π.map (fun γ => γ s) ≪ μ :=
    Measure.absolutelyContinuous_of_le_smul (hcomp s)
  have hlim : Tendsto (planInitialSecant π ℓ) (𝓝[>] (0:ℝ))
      (𝓝 (-weightedGradientPair μ hQ ν₀ u g)) := by
    apply (hvar g).congr'
    have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
      (gt_mem_nhds (show (0:ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall,self_mem_nhdsWithin] with t ht1 ht0
    exact planInitialSecant_congr_ae μ π hac hrep ⟨le_of_lt ht0,ht1.le⟩
  have hm := (measurable_path_eval (X := X) 0).prodMk (measurable_path_eval 1)
  have hD : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)) π := by
    have hd := ((continuous_fst.dist continuous_snd : Continuous (fun xy : X×X => dist xy.1 xy.2)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (p := 2) (μ := π.map (fun γ => (γ 0,γ 1))))
    exact (hd.comp_of_map hm.aemeasurable).integrable (by norm_num)
  have hmap := (optimalPlan_endpoints ν₀ ν₁ π hp).1
  have h0 : ν₀ ≪ μ := by rw [←hmap]; exact hac 0
  exact entropy_plan_signed_derivative_le μ ν₀ ν₁ h0 hpos he0 ℓ hℓ hlog π hgeo
    hmap hD K hac hconv hlim
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

 theorem transportCost_add (π σ : Measure (X×X)) :
    transportCost (π+σ) = transportCost π+transportCost σ :=
  lintegral_add_measure _ _ _

 

 theorem IsOptimalCoupling.subcoupling {ν₀ ν₁ : Measure X} {π σ : Measure (X×X)}
    [IsFiniteMeasure π] (hp : IsOptimalCoupling ν₀ ν₁ π)
    (hcost : transportCost π ≠ ∞) (hσ : σ ≤ π) :
    IsOptimalCoupling (σ.map Prod.fst) (σ.map Prod.snd) σ := by
  let δ := π-σ
  let : IsFiniteMeasure σ := isFiniteMeasure_of_le π hσ
  have hsum : δ+σ = π := Measure.sub_add_cancel_of_le hσ
  refine ⟨rfl,rfl,fun τ ht0 ht1 => ?_⟩
  have hm0 : (δ+τ).map Prod.fst = ν₀ := by
    rw [Measure.map_add _ _ measurable_fst,ht0,←Measure.map_add _ _ measurable_fst,hsum,hp.1]
  have hm1 : (δ+τ).map Prod.snd = ν₁ := by
    rw [Measure.map_add _ _ measurable_snd,ht1,←Measure.map_add _ _ measurable_snd,hsum,hp.2.1]
  have hh := hp.2.2 (δ+τ) hm0 hm1
  have hcδ : transportCost δ ≠ ∞ := by
    apply ne_top_of_le_ne_top hcost
    exact lintegral_mono' Measure.sub_le (le_refl _)
  rw [←hsum,transportCost_add,transportCost_add] at hh
  exact ENNReal.le_of_add_le_add_left hcδ hh

 

 theorem IsOptimalCoupling.replace_subcoupling {ν₀ ν₁ : Measure X}
    {π σ τ : Measure (X×X)} [IsFiniteMeasure π]
    (hp : IsOptimalCoupling ν₀ ν₁ π) (hσ : σ ≤ π)
    (hτ : IsOptimalCoupling (σ.map Prod.fst) (σ.map Prod.snd) τ) :
    IsOptimalCoupling ν₀ ν₁ (π-σ+τ) := by
  let : IsFiniteMeasure σ := isFiniteMeasure_of_le π hσ
  have hsum : π-σ+σ = π := Measure.sub_add_cancel_of_le hσ
  have hm0 : (π-σ+τ).map Prod.fst = ν₀ := by
    rw [Measure.map_add _ _ measurable_fst,hτ.1,←Measure.map_add _ _ measurable_fst,hsum,hp.1]
  have hm1 : (π-σ+τ).map Prod.snd = ν₁ := by
    rw [Measure.map_add _ _ measurable_snd,hτ.2.1,←Measure.map_add _ _ measurable_snd,hsum,hp.2.1]
  refine ⟨hm0,hm1,fun κ hk0 hk1 => ?_⟩
  calc
    transportCost (π-σ+τ) = transportCost (π-σ)+transportCost τ := transportCost_add _ _
    _ ≤ transportCost (π-σ)+transportCost σ := add_le_add (le_refl _) (hτ.2.2 σ rfl rfl)
    _ = transportCost π := by rw [←transportCost_add,hsum]
    _ ≤ transportCost κ := hp.2.2 κ hk0 hk1
 theorem transportCost_smul (a : ℝ≥0∞) (π : Measure (X×X)) :
    transportCost (a • π) = a*transportCost π := lintegral_smul_measure _ _

 
 theorem IsOptimalCoupling.smul {ν₀ ν₁ : Measure X} {π : Measure (X×X)}
    (hp : IsOptimalCoupling ν₀ ν₁ π) {a : ℝ≥0∞} (ha0 : a ≠ 0) (ha : a ≠ ∞) :
    IsOptimalCoupling (a • ν₀) (a • ν₁) (a • π) := by
  refine ⟨by rw [Measure.map_smul _ measurable_fst.aemeasurable,hp.1],
    by rw [Measure.map_smul _ measurable_snd.aemeasurable,hp.2.1],fun τ hτ0 hτ1 => ?_⟩
  have h0 : (a⁻¹ • τ).map Prod.fst = ν₀ := by
    rw [Measure.map_smul _ measurable_fst.aemeasurable,hτ0,smul_smul,
      ENNReal.inv_mul_cancel ha0 ha,one_smul]
  have h1 : (a⁻¹ • τ).map Prod.snd = ν₁ := by
    rw [Measure.map_smul _ measurable_snd.aemeasurable,hτ1,smul_smul,
      ENNReal.inv_mul_cancel ha0 ha,one_smul]
  have hh := mul_le_mul_left (hp.2.2 (a⁻¹ • τ) h0 h1) a
  rw [transportCost_smul,mul_right_comm,ENNReal.inv_mul_cancel ha0 ha,one_mul] at hh
  rw [transportCost_smul,mul_comm]
  exact hh
end

 
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

 theorem optimalPlan_replace_subplan {ν₀ ν₁ : Measure X} [IsProbabilityMeasure ν₀]
    {π σ τ : Measure C(Time,X)} [IsFiniteMeasure π]
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ) (hσ : σ ≤ π)
    (ht : IsOptimalCoupling (σ.map (fun γ => γ 0)) (σ.map (fun γ => γ 1))
      (τ.map (fun γ => (γ 0,γ 1))))
    (htg : ∀ᵐ γ ∂τ, IsGeodesic γ) :
    IsProbabilityMeasure (π-σ+τ) ∧
    (∀ᵐ γ ∂(π-σ+τ), IsGeodesic γ) ∧
    IsOptimalCoupling ν₀ ν₁ ((π-σ+τ).map (fun γ => (γ 0,γ 1))) := by
  let : IsFiniteMeasure σ := isFiniteMeasure_of_le π hσ
  have he : π-σ+σ = π := Measure.sub_add_cancel_of_le hσ
  have hpm := optimalPlan_endpoints ν₀ ν₁ π hp
  have htm := optimalPlan_endpoints _ _ τ ht
  have hm0 : (π-σ+τ).map (fun γ => γ 0) = ν₀ := by
    rw [Measure.map_add _ _ (measurable_path_eval 0),htm.1,
      ←Measure.map_add _ _ (measurable_path_eval 0),he,hpm.1]
  have hm1 : (π-σ+τ).map (fun γ => γ 1) = ν₁ := by
    rw [Measure.map_add _ _ (measurable_path_eval 1),htm.2,
      ←Measure.map_add _ _ (measurable_path_eval 1),he,hpm.2]
  have hprob : IsProbabilityMeasure (π-σ+τ) := by
    have : IsProbabilityMeasure ((π-σ+τ).map (fun γ => γ 0)) := hm0.symm ▸ inferInstance
    exact Measure.isProbabilityMeasure_of_map (measurable_path_eval 0).aemeasurable
  refine ⟨hprob,ae_add_measure_iff.mpr ⟨hg.filter_mono (ae_mono Measure.sub_le),htg⟩,?_,?_,?_⟩
  · rw [Measure.map_map measurable_fst
      ((measurable_path_eval 0).prodMk (measurable_path_eval 1))]
    exact hm0
  · rw [Measure.map_map measurable_snd
      ((measurable_path_eval 0).prodMk (measurable_path_eval 1))]
    exact hm1
  · intro κ hk0 hk1
    have hσ0 : (σ.map (fun γ => (γ 0,γ 1))).map Prod.fst = σ.map (fun γ => γ 0) := by
      rw [Measure.map_map measurable_fst
        ((measurable_path_eval 0).prodMk (measurable_path_eval 1))]
      rfl
    have hσ1 : (σ.map (fun γ => (γ 0,γ 1))).map Prod.snd = σ.map (fun γ => γ 1) := by
      rw [Measure.map_map measurable_snd
        ((measurable_path_eval 0).prodMk (measurable_path_eval 1))]
      rfl
    calc
      _ = transportCost ((π-σ).map (fun γ => (γ 0,γ 1)))+
          transportCost (τ.map (fun γ => (γ 0,γ 1))) := by
        rw [Measure.map_add _ _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1)),
          transportCost_add]
      _ ≤ transportCost ((π-σ).map (fun γ => (γ 0,γ 1)))+
          transportCost (σ.map (fun γ => (γ 0,γ 1))) :=
        add_le_add le_rfl (ht.2.2 _ hσ0 hσ1)
      _ = transportCost (π.map (fun γ => (γ 0,γ 1))) := by
        rw [←transportCost_add,←Measure.map_add _ _
          ((measurable_path_eval 0).prodMk (measurable_path_eval 1)),he]
      _ ≤ _ := hp.2.2 κ hk0 hk1

end RegularPointCoordinates

end OAI
