import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProfileAffinity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCellTransport

namespace OAI

/-! # Affinity of the profiles sampled from their actual translated Haar cells -/

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

theorem cartan_supported_cell_profile_affine_sequence
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
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
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
    (k : ℕ → cartanRootIdeal H)
    (hk : ∀ᶠ r : ℕ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale r)).equivFun (k r)‖ ≤
          Real.exp (scale r * ε r))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (profile : ℕ → F.N.carrier → S)
    (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * F.ExpN (F.N.equiv (k n))) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
      (profile n q).val z =
        rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β
        (scale n) (F.ExpN (F.N.equiv (k n)))) (profile n)) atTop (𝓝 ν))
    (U : Set (Fin (finrank ℝ H) → ℝ)) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hUne : U.Nonempty)
    (hUheight : ∀ z ∈ U, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty) :
    ∀ (f : S), f ∈ (ν : Measure S).support →
      ∃ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (b : W),
        ∀ z ∈ U, f.val z = A.val (eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G))) + b := by
  let sample := fun n y => ((F.ExpN ∘ F.N.equiv) ∘
    (M.boxBasis T hunimod eW E β (scale n)).equivFun.symm) y * F.ExpN (F.N.equiv (k n))
  let cp := fun n y => profile n (sample n y)
  have hcp n : Measurable (cp n) := (hp n).comp
    (measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN chartN hchartN
      (M.boxBasis T hunimod eW E β (scale n)) (F.ExpN (F.N.equiv (k n)))).measurable
  have hmem n y (hy : y ∈ Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ))
      (fun _ => (1 : ℝ))) : sample n y ∈
      (fun v => v * F.ExpN (F.N.equiv (k n))) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 := by
    refine ⟨((F.ExpN ∘ F.N.equiv) ∘ (M.boxBasis T hunimod eW E β (scale n)).equivFun.symm) y,
      ?_, rfl⟩
    rw [groupBox, exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one]
    exact ⟨y, hy, rfl⟩
  have hlim : Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure volume (Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
        (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
      (cp n)) atTop (𝓝 ν) := by
    convert hν using 1
    funext n
    exact M.cube_profile_law_eq_cell_profile_law T F hunimod eW haarN chartN hchartN
      b₀ E β (scale n) (F.ExpN (F.N.equiv (k n))) (profile n) (hp n)
  apply M.cartan_supported_profile_affine_sequence T F hunimod eW hExp realize haarN haarD
    dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath b₀ hE hne β γ hβ hδ hc hhi ht hcost hgap
    X hDnil hDletters bD₀ βD hβD aN hmN aD hmD scale hscale hmono hscale1 ε hεpos hε
    k hk rem hdim p x S hS cp hcp ?_ ν hlim U hU hconn hUne hUheight σ hσ
  intro n y hy z
  simpa only [cp, sample, Function.comp_apply, map_mul] using hactual n (sample n y) (hmem n y hy) z

end PolycyclicRecognition.CartanWordModel

end

end OAI
