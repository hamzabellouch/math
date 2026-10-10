import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCommonCellAffinity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFullCellAffinity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformNeighborLabels
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborBoxAffinity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborProfileAffinity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborSuffixRate
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxScaling
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanHeightRays
import Mathlib.Topology.Algebra.ConstMulAction

namespace OAI

/-! # Neighboring-sheet affinity directly from enlarged box membership -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology NNReal

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

/-- A positive enlargement works for every original neighboring-cell law.
The common affine label is derived from the published analytic inputs and
the geometric reflection argument; no affinity or label premise remains. -/
theorem exists_uniform_neighbor_common_affinity
    [IsTopologicalGroup F.N.carrier]
    [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
    [IsTopologicalGroup F.D.carrier] [Nonempty (Fin M.letterCount)]
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExp : IsGroupExponential Exp) (hinj : Function.Injective Exp)
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
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ v, chartD v = F.ExpD v)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hconv : Convex ℝ E) (hint : (interior E).Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {c lo hi : ℝ} (hc : 0 ≤ c) (hhi : 0 ≤ hi)
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
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed S] [HasOuterApproxClosed (S × S)]
    (pivot : Fin M.letterCount → H)
    (hpivot : ∀ i, eW (heightProjection T.character (pivot i)) ∈ E)
    {J : Type*} [Fintype J] (α : J → W →ₗ[ℝ] ℝ) (cap : J → ℝ)
    (hpoly : E = {w | ∀ j, α j w ≤ cap j})
    (hactive : ∀ i j, α j (eW (heightProjection T.character (pivot i))) = cap j →
      ∃ t : ℝ, 0 < t ∧ α j = t • (M.supportIn T hunimod eW).weight i)
    (B : ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (scale : ℕ → ℝ) (_hscale : Tendsto scale atTop atTop) (_hmono : StrictMono scale) (_hscale1 : ∀ n, 1 ≤ scale n)
    (R : ℕ → ℝ) (_hR0 : ∀ n, 0 ≤ R n)
    (_hR : HasSubexponentialUpperBoundSeq scale R)
    (k₀ step : ℕ → F.N.carrier)
    (_hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (_hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (profile : ℕ → F.N.carrier → S)
    (_hp : ∀ n, Measurable (profile n))
    (_hactual : ∀ n q, q ∈ (fun v => v * k₀ n) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
      (fun v => v * k₀ n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
      (profile n q).val z =
        rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (ν : ProbabilityMeasure (S × S))
    (_hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β
        (scale n) (k₀ n)) (fun q => (profile n q, profile n (q * step n)))) atTop (𝓝 ν))
    (σ : Fin M.letterCount → Bool)
    (_hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (mode : Fin M.letterCount)
    (time : ℕ → ℝ)
    (_htime : ∀ n, |time n| ≤ R n * Real.exp
      ((M.weight mode (pivot mode) + δ * B) * scale n))
    (_hroot : ∀ n, F.inclusionN (step n) =
      Exp (time n • (M.letter mode : GroupLieAlgebra (𝓘(ℝ, EG)) G))),
    ∀ (f : S × S), f ∈ (ν : Measure (S × S)).support →
      ∃ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (b₁ b₂ : W),
        ∀ z, eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' interior E →
          f.1.val z = A.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ ∧
          f.2.val z = A.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂ := by
  obtain ⟨ε, hε, hlabel⟩ := M.exists_uniform_neighbor_label_threshold T F hunimod eW
    hExp hinj realize rem π hπ hπExp chartN hchartN chartD hchartD hbijN hbijD
    dynkinN dynkinD haarN haarD b₀ E hE hconv hint pivot hpivot α cap hpoly hactive
    β hβ X hDnil bD₀ βD hβD aN hmN hdim νD hpath hΛ c B S hS
  let δ₀ := min ε (1 / (2 * (c + 1)))
  refine ⟨δ₀, lt_min hε (by positivity), ?_⟩
  intro δ hδ hd scale hscale hmono hscale1 R hR0 hR k₀ step hk₀ hstep p x
    profile hp hactual ν hν σ hσ mode time htime hroot
  have hbound : δ * (2 * (c + 1)) ≤ 1 := by
    exact (le_div_iff₀ (by positivity : 0 < 2 * (c + 1))).mp
      (hd.trans (min_le_right ε _))
  have ht : 0 < 1 - c * δ := by nlinarith [mul_nonneg hc hδ.le]
  exact M.cartan_neighbor_profiles_common_affine_of_threshold T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
    chartN hchartN b₀ hE hconv hint β γ hβ hδ hc hhi ht hcost hgap X hDnil
    hDletters bD₀ βD hβD aN hmN aD hmD scale hscale hmono hscale1 R hR0 hR
    k₀ step hk₀ hstep rem hdim p x S hS profile hp hactual ν hν σ hσ
    pivot B mode time htime hroot (hlabel δ hδ (hd.trans (min_le_left _ _)))

end PolycyclicRecognition.CartanWordModel

end

end OAI
