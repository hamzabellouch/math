import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProfileChainConcentration
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfileChainConcentration
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteModeProfileChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAllowedProfileCompactness
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfileParameterContinuity

namespace OAI

/-! # Concentration along actual finite Cartan generator chains -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set TopologicalSpace
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

/-- The actual sheet profiles concentrate along each allowed finite generator
chain. Compact containment and measurable representatives are constructed from
the Cartan geometry, so neither is an extra application hypothesis. -/
theorem cartan_raw_chain_concentration
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
    {N : ℕ} (vertex : ℕ → Fin (N + 1) → cartanRootIdeal H)
    (hvertex : ∀ n j,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale n)).equivFun
          (vertex n j)‖ ≤ Real.exp (scale n * ε n))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (profile : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →
      Fin (N + 1) → C((Fin (finrank ℝ H) → ℝ), W))
    (hactual : ∀ n y j, y ∈ Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)) → ∀ z, (profile n y j) z =
      rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
        (F.inclusionN (F.ExpN (F.N.equiv
          ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y))) *
            F.inclusionN (F.ExpN (F.N.equiv (vertex n j))))
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (U : Set (Fin (finrank ℝ H) → ℝ)) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hUne : U.Nonempty)
    (hUheight : ∀ z ∈ U, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (mode : ℕ → Fin N → Fin M.letterCount)
    (t : ℕ → Fin N → ℝ) (s : Fin M.letterCount → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (htamp : ∀ j, ∀ᶠ n in atTop,
      |t n j| ≤ B * Real.exp (scale n * (s (mode n j) + ε n)))
    (hstep : ∀ n j, F.inclusionN (F.ExpN (F.N.equiv (vertex n j.succ))) =
      F.inclusionN (F.ExpN (F.N.equiv (vertex n j.castSucc))) *
        Exp (t n j • (M.letter (mode n j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (hinterior : ∀ i, ∃ z ∈ U,
      s i < M.weight i ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z))
    (Z : Set (Fin (finrank ℝ H) → ℝ)) [CompactSpace Z] (hZU : Z ⊆ U)
    (j : Fin (N + 1)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => (cellProbabilityMeasure volume
      (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)))
      (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2 :
        Measure (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
      {y | η ≤ dist ((profile n y j).restrict Z) ((profile n y 0).restrict Z)})
      atTop (𝓝 0) := by
  classical
  let J : ℕ → G → W := fun n g => (π ((p n).val.1 g)).toAdd
  have hJ (n : ℕ) : LipschitzWith (Kπ * Λ) (J n) := hπ.comp (p n).property.1.1
  let weights := (M.supportIn T hunimod eW).weightSupport E
  let bigger := fun i => (1 + δ) * weights i
  have hbigger (i) : 0 < bigger i := mul_pos (by linarith) (hweights i)
  have hscaled : IsMaximizingColumnBasis
      (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent bigger w) β.val := by
    refine ⟨hβ.1, ?_⟩
    intro γ' hγ'
    simp only [columnBasisWeight, bigger, bracketWordExponent_const_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hβ.2 γ' hγ') (by linarith)
  obtain ⟨n₀, S, hS, hmem⟩ := exists_compact_allowed_cartan_profiles T M F
    hExp realize haarN dynkinN haarD dynkinD X hDnil hDletters bD₀ βD hβD
    b₀ weights bigger hweights hbigger β β hβ hscaled scale hscale hscale1 ε hε J hJ x
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  let r := fun n => max (Real.log (scale (n + n₀))) 0
  let φ := fun n z => F.inclusionD (F.ExpD (F.D.equiv
    ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
      (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (r n)).equivFun.symm z)))
  have hφ (n) : Continuous (φ n) :=
    F.closedD.continuous.comp (continuous_model_exp_coordinates haarD F.ExpD F.isExpD
      F.D.equiv (F.D.tangent_nilpotent inferInstance) _)
  let suffix := fun n j y =>
    F.inclusionN (F.ExpN (F.N.equiv
      ((M.boxBasis T hunimod eW E β (scale (n + n₀))).equivFun.symm y))) *
    F.inclusionN (F.ExpN (F.N.equiv (vertex (n + n₀) j)))
  have hsuffix (n j) : Continuous (suffix n j) :=
    (F.closedN.continuous.comp (continuous_model_exp_coordinates haarN F.ExpN F.isExpN
      F.N.equiv (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T)) _)).mul
        continuous_const
  let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ))
    (fun _ => (1 : ℝ))
  have hcube : cube.Nonempty := ⟨0, by constructor <;> intro i <;> norm_num⟩
  obtain ⟨sample, hsample, hsample_actual⟩ := exists_measurable_profile_chain
    (fun n => J (n + n₀)) (fun n => (hJ (n + n₀)).continuous) (fun n => x (n + n₀))
    r φ hφ suffix hsuffix cube measurableSet_Icc hcube S (by
      intro n j y hy
      apply hmem n y (vertex (n + n₀) j)
      · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
        intro i
        exact (abs_le.mpr ⟨hy.1 i, hy.2 i⟩)
      · simpa only [bigger, weights, bracketWordExponent_const_mul, boxCost] using
          hvertex (n + n₀) j)
  have hconc := M.cartan_generator_chain_concentration T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
    b₀ hE hne β γ hβ hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD (fun n => scale (n + n₀))
    (hscale.comp (tendsto_add_atTop_nat n₀))
    (hmono.comp (strictMono_id.add_const n₀)) (fun n => hscale1 (n + n₀))
    (fun n => ε (n + n₀)) (fun n => hεpos (n + n₀))
    (hε.comp (tendsto_add_atTop_nat n₀)) (fun n => vertex (n + n₀))
    (fun j => Filter.Eventually.of_forall (fun n => hvertex (n + n₀) j))
    rem hdim (fun n => p (n + n₀)) (fun n => x (n + n₀)) S hS sample hsample
    hsample_actual U hU hconn hUne hUheight σ hσ (fun n => mode (n + n₀))
    (fun n => t (n + n₀)) s hB
    (fun edge => (tendsto_add_atTop_nat n₀).eventually (htamp edge))
    (fun n => hstep (n + n₀)) hinterior Z hZU j hη
  apply (tendsto_add_atTop_iff_nat n₀).mp
  apply hconc.congr'
  filter_upwards [] with n
  apply measure_congr
  filter_upwards [ae_mem_cellProbabilityMeasure volume cube measurableSet_Icc
    (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2] with y hy
  have heq (k : Fin (N + 1)) : (sample n y k).val = profile (n + n₀) y k := by
    ext z
    exact (hsample_actual n y k hy z).trans (hactual (n + n₀) y k hy z).symm
  simp only [heq]

end PolycyclicRecognition.CartanWordModel

end

end OAI
