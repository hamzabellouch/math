import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRawChainConcentration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSuffixGeneratorSequence
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

/-- Every bounded box increment supported strictly inside the height domain
preserves the starting sheet profile in probability. Generation, prefix
bounds, compactness, and measurable profile construction are proved here. -/
theorem cartan_box_increment_concentration
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    [Nonempty (Fin M.letterCount)]
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
    (base v : ℕ → cartanRootIdeal H)
    (hbase : ∀ n,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale n)).equivFun
          (base n)‖ ≤ Real.exp (scale n * ε n))
    (s : Fin M.letterCount → ℝ)
    (hst : ∀ i, s i ≤ (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i)
    (βv : M.Bases)
    (hβv : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent s w) βv.val)
    (R : ℝ)
    (hv : ∀ n, ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList βv)
      (fun j => bracketWordExponent s (βv.val j)) (scale n)).equivFun (v n)‖ ≤ R)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (first second : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →
      C((Fin (finrank ℝ H) → ℝ), W))
    (hfirst : ∀ n y, y ∈ Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)) → ∀ z, first n y z =
      rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
        (F.inclusionN (F.ExpN (F.N.equiv
          ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y))) *
            F.inclusionN (F.ExpN (F.N.equiv (base n))))
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (hsecond : ∀ n y, y ∈ Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)) → ∀ z, second n y z =
      rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
        (F.inclusionN (F.ExpN (F.N.equiv
          ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y))) *
            F.inclusionN ((F.ExpN (F.N.equiv (base n)) * F.ExpN (F.N.equiv (v n)))))
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
    (hinterior : ∀ i, ∃ z ∈ U,
      s i < M.weight i ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z))
    (Z : Set (Fin (finrank ℝ H) → ℝ)) [CompactSpace Z] (hZU : Z ⊆ U)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => (cellProbabilityMeasure volume
      (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)))
      (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2 :
        Measure (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ))
      {y | η ≤ dist ((second n y).restrict Z) ((first n y).restrict Z)})
      atTop (𝓝 0) := by
  classical
  let weights := (M.supportIn T hunimod eW).weightSupport E
  let bigger := fun i => (1 + δ) * weights i
  have hscaled : IsMaximizingColumnBasis
      (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent bigger w) β.val := by
    refine ⟨hβ.1, ?_⟩
    intro γ' hγ'
    simp only [columnBasisWeight, bigger, bracketWordExponent_const_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hβ.2 γ' hγ') (by linarith)
  obtain ⟨N, C, hC, hgenerate⟩ := M.exists_cartan_suffix_generator_sequence T F
    hExp realize haarN dynkinN b₀ R
  obtain ⟨ε', vertex, mode, coeff, hε'pos, hε', hstart, hend, hbound, hamp, hstep⟩ :=
    hgenerate s bigger hst βv β hβv hscaled scale hscale hscale1 ε hεpos hε
      base (by simpa only [bigger, weights, bracketWordExponent_const_mul, boxCost] using hbase)
      Unit (fun n _ => v n) (fun n _ => hv n)
  let J : ℕ → G → W := fun n g => (π ((p n).val.1 g)).toAdd
  have hJ (n : ℕ) : Continuous (J n) := (hπ.comp (p n).property.1.1).continuous
  let r := fun n => max (Real.log (scale n)) 0
  let φ := fun n z => F.inclusionD (F.ExpD (F.D.equiv
    ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
      (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (r n)).equivFun.symm z)))
  have hφ (n) : Continuous (φ n) :=
    F.closedD.continuous.comp (continuous_model_exp_coordinates haarD F.ExpD F.isExpD
      F.D.equiv (F.D.tangent_nilpotent inferInstance) _)
  let suffix := fun n y j =>
    F.inclusionN (F.ExpN (F.N.equiv
      ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y))) *
      F.inclusionN (F.ExpN (F.N.equiv (vertex n () j)))
  let raw := fun n y j => rescaledContinuousProfile (J n) (hJ n) (x n)
    (suffix n y j) (r n) (φ n) (hφ n)
  have hconc := M.cartan_raw_chain_concentration T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
    b₀ hE hne β γ hβ hweights hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD scale hscale hmono hscale1 ε' hε'pos hε'
    (fun n => vertex n ())
    (by simpa only [bigger, weights, bracketWordExponent_const_mul, boxCost] using
      fun n j => hbound n () j)
    rem hdim p x raw (fun _ _ _ _ _ => rfl) U hU hconn hUne hUheight σ hσ
    (fun n => mode n ()) (fun n => coeff n ()) s (le_trans zero_le_one hC)
    (fun j => Filter.Eventually.of_forall (fun n => hamp n () j))
    (by
      intro n j
      have he := congrArg F.inclusionN (hstep n () j)
      simpa only [map_mul, F.compatibleN, LieSubmodule.coe_smul] using he)
    hinterior Z hZU (Fin.last N) hη
  apply hconc.congr'
  filter_upwards [] with n
  apply measure_congr
  filter_upwards [ae_mem_cellProbabilityMeasure volume _ measurableSet_Icc
    (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2] with y hy
  have hzero : raw n y 0 = first n y := by
    ext z
    change rescaledMapProfile (J n) (x n) (suffix n y 0) (r n) (φ n) z = _
    rw [hfirst n y hy z]
    simp only [suffix, hstart, J, r, φ]
  have hlast : raw n y (Fin.last N) = second n y := by
    ext z
    change rescaledMapProfile (J n) (x n) (suffix n y (Fin.last N)) (r n) (φ n) z = _
    rw [hsecond n y hy z]
    simp only [suffix, hend, J, r, φ]
  simp only [hzero, hlast]

end PolycyclicRecognition.CartanWordModel

end

end OAI
