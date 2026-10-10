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

/-- Both supported profiles are affine on the full inverse image of the
open contracted cell. Openness, convexity, and nonemptiness of that domain
are proved here from the surjective Cartan height map. -/
theorem cartan_neighbor_profiles_affine_on_contracted_cell
    [IsTopologicalGroup F.N.carrier]
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
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hconv : Convex ℝ E) (hint : (interior E).Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 < 1 - c * δ)
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
    (R : ℕ → ℝ) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (k₀ step : ℕ → F.N.carrier)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed S]
    (profile : ℕ → F.N.carrier → S)
    (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * k₀ n) ''
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
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β
        (scale n) (k₀ n)) (fun q => (profile n q, profile n (q * step n)))) atTop (𝓝 ν))
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty) :
    ∀ (f : S × S), f ∈ (ν : Measure (S × S)).support →
      ∃ (A₁ A₂ : templateSymmetryGroup (M.supportIn T hunimod eW)) (b₁ b₂ : W),
        ∀ z, eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' interior E →
          f.1.val z = A₁.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₁ ∧
          f.2.val z = A₂.val (eW (heightProjection T.character
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
              GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b₂ := by
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  let q := height.comp b.equivFun.symm.toLinearMap
  let U := q ⁻¹' ((fun w => (1 - c * δ) • w) '' interior E)
  have hq : Function.Surjective q := by
    intro w
    refine ⟨b.equivFun (cartanHeightSection T H (eW.symm w)), ?_⟩
    change eW (heightProjection T.character
      (b.equivFun.symm (b.equivFun (cartanHeightSection T H (eW.symm w))) :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) = w
    rw [LinearEquiv.symm_apply_apply, cartanHeightSection_height, eW.apply_symm_apply]
  have hU : IsOpen U := (isOpenMap_smul₀ ht.ne' _ isOpen_interior).preimage
    q.toContinuousLinearMap.continuous
  have hUconv : Convex ℝ U := (hconv.interior.smul (1 - c * δ)).linear_preimage q
  have hUne : U.Nonempty := by
    obtain ⟨w, hw⟩ := hint
    obtain ⟨z, hz⟩ := hq ((1 - c * δ) • w)
    exact ⟨z, w, hw, hz.symm⟩
  have haff := M.cartan_neighbor_profiles_affine_of_boxes T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
    chartN hchartN b₀ hE (hint.mono interior_subset) β γ hβ hδ hc hhi ht.le hcost hgap
    X hDnil hDletters bD₀ βD hβD aN hmN aD hmD scale hscale hmono hscale1 R hR0 hR
    k₀ step hk₀ hstep rem hdim p x S hS profile hp hactual ν hν U hU
    hUconv.isPreconnected hUne
    (fun z hz => by
      obtain ⟨w, hw, he⟩ := hz
      exact ⟨w, interior_subset hw, he⟩) σ hσ
  exact haff

end PolycyclicRecognition.CartanWordModel

end

end OAI
