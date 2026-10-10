import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLinkedChainConcentration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConcentratedProbeSelection
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLinkedProfileSelection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProfileRestriction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPivotProbePaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProbeInteriorHeights

namespace OAI

/-! # Good linked probes from the published concentration inputs -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set TopologicalSpace
open scoped Manifold Topology NNReal ENNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

variable [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

theorem exists_concentrated_linked_paths
    {K : ℕ → Type*} [∀ n, TopologicalSpace (K n)] [∀ n, CompactSpace (K n)]
    [∀ n, T2Space (K n)] [∀ n, MeasurableSpace (K n)] [∀ n, BorelSpace (K n)]
    [∀ n, Nonempty (K n)]
    [Nonempty (Fin M.letterCount)]
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
      [ErgodicSMul G (NormalizedPair G Λ) μ],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
    (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (hDletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hmN : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale) (hscale1 : ∀ n, 1 ≤ scale n)
    (ε : ℕ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (Eprobe : Fin 3 → Set W)
    (probe : Fin 3 → ∀ n, K n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (Eprobe k) β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i) scale (probe k))
    (origin base : ℕ → cartanRootIdeal H)
    (D : M.LinkedProbeChains T F hunimod eW b₀ Eprobe β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i)
      scale probe P (fun n _ => origin n) (fun n _ => base n) ε)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (pivot : H) (V : Set W) (hV : IsOpen V) (hVconv : Convex ℝ V)
    (hEc : ∀ k, IsCompact (Eprobe k)) (hEconv : ∀ k, Convex ℝ (Eprobe k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ Eprobe k)
    (hEV : ∀ k, Eprobe k ⊆ V)
    (hVheight : V ⊆ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Z : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Z ∧ Z ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      (∀ᶠ n in atTop, (br n).equivFun (scale n • pivot) ∈ Z) ∧
      ∀ [CompactSpace Z]
    (ν : ∀ n, ProbabilityMeasure (K n))
    [∀ n, (ν n : Measure (K n)).InnerRegular]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))] [HasOuterApproxClosed (C(Z, W) × C(Z, W))]
    (limitLaw : ProbabilityMeasure (C(Z, W) × C(Z, W)))
    (A : W →ₗ[ℝ] W) (b : Bool → W) (f : C(Z, W) × C(Z, W))
    (_hf : f ∈ (limitLaw : Measure _).support)
    (_haffine : ∀ s z, (if s then f.2 else f.1) z =
      A (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z.val :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b s)
    (_hlim :
      let J := fun n g => (π ((p n).val.1 g)).toAdd
      let hJ := fun n => (hπ.comp (p n).property.1.1).continuous
      let r := fun n => max (Real.log (scale n)) 0
      let bN := fun n => M.boxBasis T hunimod eW E β (scale n)
      let bD := fun n => exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (r n)
      Tendsto (fun n => ProbabilityMeasure.map
        (cellProbabilityMeasure volume
          (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)))
          (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
        (fun y =>
          ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
            (origin n)).restrict Z,
           (F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) y
            (base n)).restrict Z))) atTop (𝓝 limitLaw)),
    let J := fun n g => (π ((p n).val.1 g)).toAdd
    let hJ := fun n => (hπ.comp (p n).property.1.1).continuous
    let r := fun n => max (Real.log (scale n)) 0
    let bN := fun n => M.boxBasis T hunimod eW E β (scale n)
    let bD := fun n => exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords d) βD)
      (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (r n)
    let q := fun z : Z => eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z.val :
        GroupLieAlgebra (𝓘(ℝ, EG)) G))
    ∃ (η : ℕ → ℝ) (sample : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
      (good : ∀ n, Set (K n)),
      (∀ n, 0 < η n) ∧ Tendsto η atTop (𝓝 0) ∧
      (∀ n, IsCompact (good n) ∧ MeasurableSet (good n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (K n)) (good n)) ∧
      ∀ᶠ n in atTop,
        sample n ∈ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) ∧
        (∀ (s : Bool) (z : Z),
          ‖F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (sample n)
            (if s then base n else origin n) z - (A (q z) + b s)‖ < η n) ∧
        (∀ y ∈ good n, ∀ (k : Fin 3) (j : Fin ((P k).length + 1)) (z : Z),
          ‖F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n) (bN n) (bD n) (sample n)
            (D.vertex k n y j) z - (A (q z) + b (k != 0))‖ < 2 * η n) ∧
        ∀ y ∈ good n, ∀ k : Fin 3,
          ∃ path : Path (1 : G) (basedImage (p n).val.1
              (x n * F.sampledProbeSuffix (bN n) (sample n) (D.vertex k n y 0) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
              (x n * F.sampledProbeSuffix (bN n) (sample n)
                  (D.vertex k n y (Fin.last (P k).length)) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))),
            PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
            ∀ t, ∃ w ∈ (fun z => A (z - h pivot)) '' Eprobe k,
              ‖(π (path t)).toAdd - scale n • w‖ ≤
                4 * scale n * η n + C * (1 + Real.log (2 + scale n)) := by
  dsimp only
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
  let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
  let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  let U := {z | h (b.equivFun.symm z) ∈ V}
  have hU : IsOpen U := hV.preimage
    (h.comp b.equivFun.symm.toLinearMap).continuous_of_finiteDimensional
  have hconn : IsPreconnected U :=
    (hVconv.linear_preimage (h.comp b.equivFun.symm.toLinearMap)).isPreconnected
  have hUne : U.Nonempty := ⟨b.equivFun pivot, by
    change eW (heightProjection T.character (b.equivFun.symm (b.equivFun pivot) :
      GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ V
    rw [LinearEquiv.symm_apply_apply]
    exact hEV 0 (hpivot 0)⟩
  have hUheight : ∀ z ∈ U, eW (heightProjection T.character
      (b.equivFun.symm z : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈
      (fun w => (1 - c * δ) • w) '' E := fun _ hz => hVheight hz
  have hinterior (k : Fin 3) (i : Fin M.letterCount) : ∃ z ∈ U,
      (M.supportIn T hunimod eW).weightSupport (Eprobe k) i <
        M.weight i (b.equivFun.symm z) :=
    M.exists_probe_switching_height T hunimod eW b (hEc k) ⟨_, hpivot k⟩ hV (hEV k) i
  obtain ⟨Z, C, hZ, hZV, hp, hC, hpaths⟩ :=
    M.exists_linked_probe_paths_with_pivot T F hunimod eW hExp realize haarD dynkinD
      π hπExp hπ X hDnil bD₀ βD hβD scale hscale
      (fun n => lt_of_lt_of_le zero_lt_one (hscale1 n)) pivot Eprobe V hEc hEconv
      hpivot hV hVconv hEV b₀ β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i)
      probe P (fun n _ => origin n) (fun n _ => base n) ε D
      (fun n => M.boxBasis T hunimod eW E β (scale n)) hD Λ
  refine ⟨Z, C, hZ, hZV, hC, hp, ?_⟩
  intro instZ ν instν instMeas instBorel instProd instOuter limitLaw A bval f hf haffine hlim
  obtain ⟨η, sample, good, hη0, hη, hg, he⟩ :=
    M.select_linked_profiles_of_published_inputs T F hunimod eW hExp realize haarN haarD
      dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath b₀ hE hne β γ hβ hweights
      hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD aN hmN aD hmD
      scale hscale hmono hscale1 ε hεpos hε Eprobe probe P origin base D rem hdim p x
      hN hD U hU hconn hUne hUheight σ hσ hinterior Z hZV ν limitLaw A bval f hf haffine hlim
  refine ⟨η, sample, good, hη0, hη, hg, ?_⟩
  filter_upwards [he, hpaths] with n hn hnpaths
  refine ⟨hn.1, hn.2.1, hn.2.2, ?_⟩
  intro y hy k
  have hr : max (Real.log (scale n)) 0 = Real.log (scale n) :=
    max_eq_left (Real.log_nonneg (hscale1 n))
  have hgood (j : Fin ((P k).length + 1)) (z) (hz : z ∈ Z) :
      ‖F.sampledProbeProfile hD (fun g => (π ((p n).val.1 g)).toAdd)
        ((hπ.comp (p n).property.1.1).continuous) (x n) (Real.log (scale n))
        (M.boxBasis T hunimod eW E β (scale n)) (br n) (sample n)
        (D.vertex k n y j) z - (A (eW (heightProjection T.character
          (b.equivFun.symm z : GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval (k != 0))‖ ≤ 2 * η n := by
    simpa only [hr] using (hn.2.2 y hy k j ⟨z, hz⟩).le
  obtain ⟨path, hm, hh⟩ := hnpaths k y (x n) (sample n) (p n).val.1 (p n).property.1.1
    A (bval (k != 0)) (2 * η n) hgood
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hr] using path
  · exact hm
  · intro t
    obtain ⟨w, hw, hb⟩ := hh t
    exact ⟨w, hw, by nlinarith [hb]⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
