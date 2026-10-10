import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTwoPathProbeRestrictions
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProbeCoordinateRegions
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasuredProbeRegions

namespace OAI

/-! # Actual probe restrictions with their Haar volume bounds -/

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
/-- The two actual target paths give quotient/ideal/Cartan regions in one
fixed section. All their volume estimates follow from exponential Haar
coordinates, and no target-coordinate volume bound is an assumption. -/
theorem exists_measured_two_path_probe_regions
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
    (scale η : ℕ → ℝ) (hmono : StrictMono scale) (hscale : Tendsto scale atTop atTop)
    (hscale1 : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n)
    (hη : Tendsto η atTop (𝓝 0)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    let μK := Measure.map (kernelRealization πQ ιI hιI hrange) μI
    let P₂ := ∑ j, M.coneIdealWordCost C
      ((M.supportIn T hunimod eW).weightSupport E₂) (β₂.val j)
    ∃ R : MeasuredProbeRegions πQ μQ μK ν scale P₂,
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          π cell E₁ E₂ η A B δ n := by
  dsimp only
  obtain ⟨bQ, lift, hlift, RQ, S, RD, hdata⟩ :=
    M.exists_two_path_probe_restrictions T F hunimod eW π hπExp chartN hchartN
      chartD hchartD dynkinN dynkinD hbijN hbijD b₀ γ₀ hcell hφ hpath hKπ hLip
      C Q ExpQ hExpQ hbijQ haarQ πQ hπQ μQ α act hact E₁ E₂ hE₁ hne₁ hE₂ hne₂
      β₁ hβ₁ hz₁ bI₀ β₂ hβ₂ hs₂ hz₂ hp₂ scale η hmono hscale hscale1 hη0 hη A B hA hB
  have hRQ := hdata.1
  have hRQvol := hdata.2.1
  have hS0 := hdata.2.2.1
  have hRD0 := hdata.2.2.2.1
  have hS := hdata.2.2.2.2.1
  have hRD := hdata.2.2.2.2.2.1
  let δ₀ := Classical.choose hdata.2.2.2.2.2.2
  have hδ₀ := (Classical.choose_spec hdata.2.2.2.2.2.2).1
  have hrestrict := (Classical.choose_spec hdata.2.2.2.2.2.2).2
  have hqcompat (v : cartanRootIdeal H) : πQ (chartN (F.N.equiv v)) =
      chartQ (Q.equiv ((M.coneWordIdeal C).toSubmodule.mkQ v)) :=
    (congrArg πQ (hchartN (F.N.equiv v))).trans ((hπQ v).trans (hchartQ _).symm)
  have hzQ : chartQ (Q.equiv 0) = 1 := by
    rw [map_zero, hchartQ, hExpQ.map_zero]
  have hregions :=
    M.exists_ideal_cartan_probe_regions F C Q chartN hchartN chartQ πQ hqcompat hzQ
      bQ lift hlift I ExpI hExpI haarI ιI hιI hrange hIExp μI ν haarD hbijD
      ((M.supportIn T hunimod eW).weightSupport E₂) β₂ scale S RD hscale hS0 hRD0 hS hRD
  let σ := Classical.choose hregions
  have hr₁ := Classical.choose_spec hregions
  let hσ := Classical.choose hr₁
  have hr₂ := Classical.choose_spec hr₁
  let RI := Classical.choose hr₂
  have hr₃ := Classical.choose_spec hr₂
  let BD := Classical.choose hr₃
  have hr₄ := Classical.choose_spec hr₃
  let V := Classical.choose hr₄
  have hregion := Classical.choose_spec hr₄
  have hfinite := hregion.1
  have hV := hregion.2.1
  have hV0 := hregion.2.2.1
  have hDvol := hregion.2.2.2.1
  have hIvol := hregion.2.2.2.2.1
  have hcoord := hregion.2.2.2.2.2
  let R : MeasuredProbeRegions πQ μQ
      (Measure.map (kernelRealization πQ ιI hιI hrange) μI) ν scale
      (∑ j, M.coneIdealWordCost C ((M.supportIn T hunimod eW).weightSupport E₂) (β₂.val j)) :=
    { sectionMap := σ
      section_rightInverse := hσ
      quotientRegion := RQ
      idealRegion := RI
      cartanRegion := BD
      idealLoss := V
      quotient_finite := hRQ
      ideal_finite := fun n => (hfinite n).1
      cartan_finite := fun n => (hfinite n).2
      quotient_subexponential := hRQvol
      ideal_subexponential := hV
      idealLoss_nonneg := hV0
      cartan_subexponential := hDvol
      ideal_volume := hIvol }
  refine ⟨R, δ₀, hδ₀, ?_⟩
  intro δ hδ hδle
  filter_upwards [hrestrict δ hδ hδle] with n hn
  intro base anchor first second path₁ path₂ hm₁ hm₂ hh₁ hh₂ hsmall hdist
  exact map_cell_lift_conditions
    (hn base anchor first second path₁ path₂ hm₁ hm₂ hh₁ hh₂ hsmall hdist)
    (fun u d z _ hz => ⟨hz.1,
      hcoord n (u * F.action d z.1) (d * z.2) hz.2.1 hz.2.2⟩)

end PolycyclicRecognition.CartanWordModel

end

end OAI
