import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConcentratedRootFrames
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRestrictedNeighborLaw
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSampledProbeFrames
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProfilePivot
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLinkedChainConcentration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConcentratedProbeSelection
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLinkedProfileSelection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProfileRestriction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPivotProbePaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProbeInteriorHeights

namespace OAI

/-! # Concentration from the original neighboring-cell law -/

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

variable [IsTopologicalGroup F.N.carrier]

/-- The original Haar neighboring law supplies the restricted law used by
concentration. The sampled points retain the original center. -/
theorem exists_original_neighbor_root_frames
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
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (baseGroup step : ℕ → F.N.carrier)
    (horigin : ∀ n, F.ExpN (F.N.equiv (origin n)) = baseGroup n)
    (hbase : ∀ n, F.ExpN (F.N.equiv (base n)) = baseGroup n * step n)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    (profile : ℕ → F.N.carrier → S) (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * baseGroup n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
      (fun v => v * baseGroup n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (scale n)) 0))) z)
    (law : ProbabilityMeasure (S × S))
    (hlaw : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        E β (scale n) (baseGroup n)) (fun q => (profile n q, profile n (q * step n))))
      atTop (𝓝 law))
    (A : W →ₗ[ℝ] W) (bval : Bool → W) (f : S × S)
    (hf : f ∈ (law : Measure (S × S)).support)
    (haffine : ∀ s z,
      eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ V →
      (if s then f.2 else f.1).val z = A (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval s) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Z : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Z ∧ Z ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∃ z₀ : ℕ → Z,
      (∀ᶠ n in atTop,
        F.profileChart (br n) (z₀ n).val =
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∧
        h (b.equivFun.symm (z₀ n).val) = h pivot) ∧
      ∀ [CompactSpace Z]
    (ν : ∀ n, ProbabilityMeasure (K n))
    [∀ n, (ν n : Measure (K n)).InnerRegular]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))] [HasOuterApproxClosed (C(Z, W) × C(Z, W))],
    let chart := fun n (z : Z) => F.profileChart (br n) z.val
    let q := fun z : Z => h (b.equivFun.symm z.val)
    ∃ (η : ℕ → ℝ) (sample : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
      (good : ∀ n, Set (K n)),
      (∀ n, 0 < η n) ∧ Tendsto η atTop (𝓝 0) ∧
      (∀ n, IsCompact (good n) ∧ MeasurableSet (good n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (K n)) (good n)) ∧
      ∀ᶠ n in atTop,
        (∀ s : Bool,
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN (F.sampleRoot (M.boxBasis T hunimod eW E β (scale n)) (sample n) *
              F.ExpN (F.N.equiv (if s then base n else origin n)))) (Real.log (scale n))
            (chart n) (z₀ n) - (A (q (z₀ n)) + bval s)‖ < η n) ∧
        (∀ y ∈ good n, ∀ (k : Fin 3) (j : Fin ((P k).length + 1)),
          ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN (F.sampleRoot (M.boxBasis T hunimod eW E β (scale n)) (sample n) *
              F.ExpN (F.N.equiv (D.vertex k n y j)))) (Real.log (scale n))
            (chart n) (z₀ n) - (A (q (z₀ n)) + bval (k != 0))‖ < 2 * η n) ∧
        ∀ y ∈ good n, ∀ k : Fin 3,
          ∃ path : Path (1 : G) (basedImage (p n).val.1
              (x n * F.inclusionN (F.sampleRoot (M.boxBasis T hunimod eW E β (scale n))
                (sample n) * F.ExpN (F.N.equiv (D.vertex k n y 0))) * chart n (z₀ n))
              (x n * F.inclusionN (F.sampleRoot (M.boxBasis T hunimod eW E β (scale n))
                (sample n) * F.ExpN (F.N.equiv (D.vertex k n y (Fin.last (P k).length)))) * chart n (z₀ n))),
            PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
            ∀ t, ∃ w ∈ (fun z => A (z - h pivot)) '' Eprobe k,
              ‖(π (path t)).toAdd - scale n • w‖ ≤
                4 * scale n * η n + C * (1 + Real.log (2 + scale n)) := by
  obtain ⟨Z, C, hZ, hZV, hC, z₀, hz₀, hframes⟩ :=
    M.exists_concentrated_root_frames T F hunimod eW hExp realize haarN haarD
      dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath b₀ hE hne β γ hβ hweights
      hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD aN hmN aD hmD
      scale hscale hmono hscale1 ε hεpos hε Eprobe probe P origin base D rem hdim p x
      hN hD pivot V hV hVconv hEc hEconv hpivot hEV hVheight σ hσ
  refine ⟨Z, C, hZ, hZV, hC, z₀, hz₀, ?_⟩
  intro instCompact ν instInner instMeas instBorel instProdBorel instApprox
  have hrestricted := M.restricted_neighbor_cube_law T F hunimod eW haarN
    chartN hchartN b₀ E β scale (fun n => max (Real.log (scale n)) 0)
    baseGroup step origin base horigin hbase hD
    (fun n g => (π ((p n).val.1 g)).toAdd)
    (fun n => (hπ.comp (p n).property.1.1).continuous) x
    (fun n => exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords d) βD)
      (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
      (max (Real.log (scale n)) 0)) S profile hp hactual law hlaw Z f hf
  apply hframes ν (ProbabilityMeasure.map law
    (fun g : S × S => (g.1.val.restrict Z, g.2.val.restrict Z))) A bval
    (f.1.val.restrict Z, f.2.val.restrict Z) hrestricted.2
  · intro s z
    cases s with
    | false => simpa using haffine false z.val (hZV z.property)
    | true => simpa using haffine true z.val (hZV z.property)
  · exact hrestricted.1

end PolycyclicRecognition.CartanWordModel

end

end OAI
