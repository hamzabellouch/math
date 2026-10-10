import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarRegionMeasure
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMeasuredConeCells

namespace OAI

/-! # The fixed target measure and trace on a transformed polar cone -/

noncomputable section
namespace PolycyclicRecognition

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
  [IsTopologicalGroup F.N.carrier]

/-- Normalize only the target quotient Haar measure. The published action,
its exact trace, and every later path region use this same fixed product
measure on the nilpotent factor. -/
theorem MeasuredCone.exists_fixed_polar_target_regions
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
    let E₂ := A '' normalizedPolarTemplates K ε 2
    ∃ (α : F.D.carrier →* MulAut D.Q.carrier) (act : G →* Equiv.Perm D.Q.carrier)
      (μQ : Measure D.Q.carrier) (c : Fin M.letterCount → ℕ)
      (β₂ : M.ConeIdealBases C),
      ∃ hμQ : μQ.IsHaarMeasure,
      let D' := D.withQuotientHaar M F C μQ hμQ
      let μN := D'.sectionMeasure M F C D'.maps.sectionMap D'.maps.section_rightInverse
      (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = D.maps.quotient n * α d q) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∉
        transformedPolarCone K A → c i = 0) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈
        transformedPolarCone K A → 0 < c i) ∧
      (∀ g E, μQ (act g '' E) = ENNReal.ofReal (Real.exp
        ((∑ i, (c i : ℝ) • ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
          (height g).toAdd)) * μQ E) ∧
      M.IsMaximizingConeIdealBasis C bI ((M.supportIn T hunimod eW).weightSupport E₂) β₂ ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale : ℕ → ℝ),
        StrictMono scale → Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
        ∀ (w : W) (δ : ℝ), 0 < δ → δ ≤ δ₀ →
        ∀ (η : ℕ → ℝ), (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
        ∀ Cp : ℝ, 0 ≤ Cp →
        ∃ R : MeasuredProbeRegions D.maps.quotient μQ
          (D.kernelMeasure M F C) ν scale
          (∑ j, M.coneIdealWordCost C
            ((M.supportIn T hunimod eW).weightSupport E₂) (β₂.val j)),
          μN = Measure.map (quotientSectionHomeomorph D.maps.quotient
            D.maps.quotient_continuous R.sectionMap R.section_rightInverse).symm
            (μQ.prod (D.kernelMeasure M F C)) ∧
          ∀ᶠ n in atTop, R.ControlsTwoPaths
            (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
            height cell
            ((fun z => A (z - w)) '' polarSamplingTemplates K ε w 0)
            ((fun z => A (z - w)) '' polarSamplingTemplates K ε w 2)
            (fun n => 2 * η n) Cp Cp δ n := by
  dsimp only
  obtain ⟨α, act, μQ, c, β₂, hμQ, hact, hout, hin, hHaar, hβ₂, δ₀, hδ₀, hregions⟩ :=
    D.exists_uniform_polar_target_regions M F T hunimod eW
      hExp realize hNbij hDbij dynkinN dynkinD chartN hchartN chartD hchartD
      height hheight hpath hLheight hLip K A hK haarQ haarI haarD ν bN bI γ₀ hcell hε
  refine ⟨α, act, μQ, c, β₂, hμQ, hact, hout, hin, hHaar, hβ₂, δ₀, hδ₀, ?_⟩
  intro scale hs hscale hs1 w δ hδ hd η hη0 hη Cp hCp
  let C := heightConePreimage (H := H) T eW (transformedPolarCone K A)
  let D' := D.withQuotientHaar M F C μQ hμQ
  exact D'.fixed_polar_region_factory M F C K A.toLinearMap ε w height act ν cell
    scale _ δ δ₀ hδ hd
    (fun η hη0 hη Cp Clog hCp hClog =>
      hregions scale η hs hscale hs1 hη0 hη Cp Clog hCp hClog)
    η hη0 hη Cp hCp

end CartanWordModel
end PolycyclicRecognition

end

end OAI
