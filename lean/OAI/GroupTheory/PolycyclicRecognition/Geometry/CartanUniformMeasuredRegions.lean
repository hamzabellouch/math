import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMeasuredRegionsFromLifts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformTwoPathRestrictions

namespace OAI

/-! # Measured probe regions with the threshold fixed before the paths -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
open scoped Manifold Topology
open MeasureTheory

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)

include hunimod hπExp hchartN hchartD dynkinN dynkinD in
theorem exists_uniform_measured_probe_regions
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases) {cell : Set (F.N.carrier × F.D.carrier)} (hcell : IsCompact cell)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hbijN dynkinN (cartanLog H F.D.equiv F.ExpD hbijD d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kπ : ℝ} (hKπ : 0 ≤ Kπ)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Kπ * dist x y)
    (C : Set (H →ₗ[ℝ] ℝ))
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ) (hbijQ : Function.Bijective ExpQ)
    (haarQ : NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hπQ : ∀ v, πQ (F.ExpN (F.N.equiv v)) = ExpQ (Q.equiv (M.coneProjection C v)))
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchartQ : ∀ v, chartQ v = ExpQ v)
    (μQ : Measure Q.carrier) [μQ.IsHaarMeasure]
    (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = πQ u * α d q)
    (I : NilpotentLieModel (M.coneWordIdeal C))
    (ExpI : GroupLieAlgebra (𝓘(ℝ, I.modelSpace)) I.carrier → I.carrier)
    (hExpI : IsGroupExponential ExpI)
    (haarI : NilpotentExponentialHaarInput I.modelSpace I.carrier)
    (ιI : I.carrier →* F.N.carrier) (hιI : Topology.IsClosedEmbedding ιI)
    (hrange : range ιI = (πQ.ker : Set F.N.carrier))
    (hIExp : ∀ i : M.coneWordIdeal C,
      ιI (ExpI (I.equiv i)) = F.ExpN (F.N.equiv (i : cartanRootIdeal H)))
    (μI : Measure I.carrier) [μI.IsHaarMeasure]
    (ν : Measure F.D.carrier) [ν.IsHaarMeasure]
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (E₁ E₂ : Set W) (hE₁ : IsCompact E₁) (hne₁ : E₁.Nonempty)
    (hE₂ : IsCompact E₂) (hne₂ : E₂.Nonempty)
    (β₁ : M.Bases)
    (hβ₁ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E₁) β₁.val)
    (hz₁ : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E₁ i = 0)
    (bI₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (β₂ : M.ConeIdealBases C)
    (hβ₂ : M.IsMaximizingConeIdealBasis C bI₀
      ((M.supportIn T hunimod eW).weightSupport E₂) β₂)
    (hs₂ : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E₂ i)
    (hz₂ : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E₂ i = 0)
    (hp₂ : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C →
      0 < (M.supportIn T hunimod eW).weightSupport E₂ i)
    :
    let μK := Measure.map (kernelRealization πQ ιI hιI hrange) μI
    let P₂ := ∑ j, M.coneIdealWordCost C
      ((M.supportIn T hunimod eW).weightSupport E₂) (β₂.val j)
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (scale η : ℕ → ℝ),
      StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 1 ≤ scale n) → (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ R : MeasuredProbeRegions πQ μQ μK ν scale P₂,
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          π cell E₁ E₂ η A B δ n := by
  dsimp only
  obtain ⟨bQ, lift, hlift, δ₀, hδ₀, hdata⟩ :=
    M.exists_uniform_two_path_probe_restrictions T F hunimod eW π hπExp chartN hchartN
      chartD hchartD dynkinN dynkinD hbijN hbijD b₀ γ₀ hcell hφ hpath hKπ hLip
      C Q ExpQ hExpQ hbijQ haarQ πQ hπQ μQ α act hact E₁ E₂ hE₁ hne₁ hE₂ hne₂
      β₁ hβ₁ hz₁ bI₀ β₂ hβ₂ hs₂ hz₂ hp₂
  have hqcompat (v : cartanRootIdeal H) : πQ (chartN (F.N.equiv v)) =
      chartQ (Q.equiv ((M.coneWordIdeal C).toSubmodule.mkQ v)) :=
    (congrArg πQ (hchartN (F.N.equiv v))).trans ((hπQ v).trans (hchartQ _).symm)
  have hzQ : chartQ (Q.equiv 0) = 1 :=
    (congrArg chartQ (map_zero Q.equiv)).trans
      ((hchartQ 0).trans hExpQ.map_zero)
  refine ⟨δ₀, hδ₀, ?_⟩
  exact M.measured_probe_regions_of_uniform_lifts F C Q chartN hchartN chartQ πQ
    hqcompat hzQ bQ lift hlift I ExpI hExpI haarI ιI hιI hrange hIExp μI ν haarD hbijD
    ((M.supportIn T hunimod eW).weightSupport E₂) β₂ π act cell E₁ E₂ μQ δ₀ hdata



end PolycyclicRecognition.CartanWordModel

end

end OAI
