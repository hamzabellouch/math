import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPublishedPolarAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformMeasuredRegions
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTransformedPolarTemplates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarTiledChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorCharts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMeasuredConeHaar
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSamplingParameters

namespace OAI

/-! # The actual target regions and Haar trace for a transformed polar cone -/

noncomputable section
namespace PolycyclicRecognition

theorem recentered_polarSamplingTemplates
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (K : ProperCone ℝ (StrongDual ℝ W)) (ε : ℝ) (w : W)
    (A : W →ₗ[ℝ] W) (k : Fin 3) :
    (fun z => A (z - w)) '' polarSamplingTemplates K ε w k =
      A '' normalizedPolarTemplates K ε k := by
  simp only [polarSamplingTemplates, normalizedPolarTemplates, Set.image_image,
    add_sub_cancel_right]

namespace CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory Metric Filter
open scoped Manifold BigOperators Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsIsometricSMul G G] [ProperSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The transformed polar geometry supplies a maximizing ideal basis and
a path threshold for an already specified compatible quotient action. -/
theorem MeasuredCone.uniform_polar_regions_of_action
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hNbij : Function.Bijective F.ExpN) (hDbij : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ v, chartD v = F.ExpD v)
    (height : G →* Multiplicative W)
    (hheight : ∀ v, (height (Exp v)).toAdd = eW (heightProjection T.character v))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Lheight : ℝ} (hLheight : 0 ≤ Lheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Lheight * dist x y)
    (K : ProperCone ℝ (StrongDual ℝ W)) (A : W ≃ₗ[ℝ] W)
    (D : M.MeasuredCone F (heightConePreimage T eW (transformedPolarCone K A)))
    (haarQ : NilpotentExponentialHaarInput D.Q.modelSpace D.Q.carrier)
    (haarI : NilpotentExponentialHaarInput D.I.modelSpace D.I.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure]
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A))))
    (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    {ε : ℝ} (hε : 0 < ε)
    (μQ : Measure D.Q.carrier) [μQ.IsHaarMeasure]
    (α : F.D.carrier →* MulAut D.Q.carrier) (act : G →* Equiv.Perm D.Q.carrier)
    (hact : ∀ n d q, act (F.inclusionN n * F.inclusionD d) q = D.maps.quotient n * α d q) :
    let C := heightConePreimage T eW (transformedPolarCone K A)
    let E₁ := A '' normalizedPolarTemplates K ε 0
    let E₂ := A '' normalizedPolarTemplates K ε 2
    ∃ β₂ : M.ConeIdealBases C,
      M.IsMaximizingConeIdealBasis C bI ((M.supportIn T hunimod eW).weightSupport E₂) β₂ ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
        (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ Cp Clog : ℝ, 0 ≤ Cp → 0 ≤ Clog →
        ∃ R : MeasuredProbeRegions D.maps.quotient μQ
          (D.kernelMeasure M F C) ν scale
          (∑ j, M.coneIdealWordCost C
            ((M.supportIn T hunimod eW).weightSupport E₂) (β₂.val j)),
          ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∀ᶠ n in atTop, R.ControlsTwoPaths
            (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
            height cell E₁ E₂ η Cp Clog δ n := by
  dsimp only
  let C := heightConePreimage (H := H) T eW (transformedPolarCone K A)
  let E₁ := A '' normalizedPolarTemplates K ε 0
  let E₂ := A '' normalizedPolarTemplates K ε 2
  let : D.measures.measureI.IsHaarMeasure := D.measures.haarI
  obtain ⟨β₂, hβ₂all⟩ := M.exists_transformed_polar_probe_basis T hunimod eW K A bI
  have hβ₂ : M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport E₂) β₂ :=
    hβ₂all (ε / 3) (by positivity)
  obtain ⟨hE₁, _, hz₁, _, hzero₁, _⟩ :=
    M.transformed_polar_width_properties T hunimod eW K A
      (c := 2 * ε / 3) (by positivity)
  obtain ⟨hE₂, _, hz₂, hs₂, hzero₂, hpos₂⟩ :=
    M.transformed_polar_width_properties T hunimod eW K A
      (c := ε / 3) (by positivity)
  obtain ⟨β₁, hβ₁, _⟩ := M.exists_maximizing_box_basis T hunimod eW bN E₁
  have hφ (d : F.D.carrier) : F.action d =
      M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hNbij dynkinN
        (cartanLog H F.D.equiv F.ExpD hDbij d) :=
    cartan_action_eq_adjoint_of_published_realization T M F hExp realize hNbij hDbij dynkinN d
  have factory : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
        (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ Cp Clog : ℝ, 0 ≤ Cp → 0 ≤ Clog →
        ∃ R : MeasuredProbeRegions D.maps.quotient μQ
          (D.kernelMeasure M F C) ν scale
          (∑ j, M.coneIdealWordCost C
            ((M.supportIn T hunimod eW).weightSupport E₂) (β₂.val j)),
          ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∀ᶠ n in atTop, R.ControlsTwoPaths
            (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
            height cell E₁ E₂ η Cp Clog δ n := by
    exact exists_uniform_measured_probe_regions
      (EG := EG) (G := G) (W := W) T M F hunimod eW
      height hheight chartN hchartN chartD hchartD dynkinN dynkinD hNbij hDbij
      bN γ₀ hcell hφ hpath hLheight hLip C D.Q D.maps.expQ D.maps.isExpQ
      (funext D.maps.chartQ_eq ▸ D.maps.chartQ.bijective) haarQ D.maps.quotient
      D.maps.quotient_exp D.maps.chartQ D.maps.chartQ_eq μQ α act hact
      D.I D.maps.expI D.maps.isExpI haarI D.maps.inclusion D.maps.inclusion_closed
      D.maps.inclusion_range D.maps.inclusion_exp D.measures.measureI ν haarD
      E₁ E₂ hE₁ ⟨0, hz₁⟩ hE₂ ⟨0, hz₂⟩ β₁ hβ₁ hzero₁ bI β₂ hβ₂ hs₂ hzero₂ hpos₂
  obtain ⟨δ₀, hδ₀, hregions⟩ := factory
  exact ⟨β₂, hβ₂, δ₀, hδ₀, hregions⟩

/-- The action, its positive pure-word trace, the maximizing target basis,
and the uniform path-restriction regions all belong to one actual target
quotient. The region threshold is fixed before the scale or concentration
errors are chosen. -/
theorem MeasuredCone.exists_uniform_polar_target_regions
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (hNbij : Function.Bijective F.ExpN) (hDbij : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ v, chartD v = F.ExpD v)
    (height : G →* Multiplicative W)
    (hheight : ∀ v, (height (Exp v)).toAdd = eW (heightProjection T.character v))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Lheight : ℝ} (hLheight : 0 ≤ Lheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Lheight * dist x y)
    (K : ProperCone ℝ (StrongDual ℝ W)) (A : W ≃ₗ[ℝ] W)
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
    (D : M.MeasuredCone F (heightConePreimage T eW (transformedPolarCone K A)))
    (haarQ : NilpotentExponentialHaarInput D.Q.modelSpace D.Q.carrier)
    (haarI : NilpotentExponentialHaarInput D.I.modelSpace D.I.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure]
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A))))
    (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    {ε : ℝ} (hε : 0 < ε) :
    let C := heightConePreimage (H := H) T eW (transformedPolarCone K A)
    let E₁ := A '' normalizedPolarTemplates K ε 0
    let E₂ := A '' normalizedPolarTemplates K ε 2
    ∃ (α : F.D.carrier →* MulAut D.Q.carrier) (act : G →* Equiv.Perm D.Q.carrier)
      (μQ : Measure D.Q.carrier) (c : Fin M.letterCount → ℕ)
      (β₂ : M.ConeIdealBases C),
      μQ.IsHaarMeasure ∧
      (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = D.maps.quotient n * α d q) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∉
        transformedPolarCone K A → c i = 0) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈
        transformedPolarCone K A → 0 < c i) ∧
      (∀ g E, μQ (act g '' E) = ENNReal.ofReal (Real.exp
        ((∑ i, (c i : ℝ) • ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
          (height g).toAdd)) * μQ E) ∧
      M.IsMaximizingConeIdealBasis C bI ((M.supportIn T hunimod eW).weightSupport E₂) β₂ ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
        (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ Cp Clog : ℝ, 0 ≤ Cp → 0 ≤ Clog →
        ∃ R : MeasuredProbeRegions D.maps.quotient μQ
          (D.kernelMeasure M F C) ν scale
          (∑ j, M.coneIdealWordCost C
            ((M.supportIn T hunimod eW).weightSupport E₂) (β₂.val j)),
          ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∀ᶠ n in atTop, R.ControlsTwoPaths
            (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
            height cell E₁ E₂ η Cp Clog δ n := by
  dsimp only
  obtain ⟨α, act, μQ, c, hμQ, _, hact, hout, hin, hHaar⟩ :=
    MeasuredCone.polar_action_haar_of_published_realization
      (EG := EG) (G := G) (W := W)
      M F T hunimod eW hExp realize hNbij hDbij dynkinN (transformedPolarCone K A)
      (transformedPolarCone_salient K A hK) D haarQ height hheight
  let : μQ.IsHaarMeasure := hμQ
  obtain ⟨β₂, hβ₂, δ₀, hδ₀, hregions⟩ :=
    D.uniform_polar_regions_of_action M F T hunimod eW
      hExp realize hNbij hDbij dynkinN dynkinD chartN hchartN chartD hchartD
      height hheight hpath hLheight hLip K A haarQ haarI haarD ν bN bI γ₀ hcell hε
      μQ α act hact
  exact ⟨α, act, μQ, c, β₂, hμQ, hact, hout, hin, hHaar, hβ₂, δ₀, hδ₀, hregions⟩

end CartanWordModel
end PolycyclicRecognition

end

end OAI
