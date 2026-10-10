import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanIndependentChainConcentration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActualProbeProfiles

namespace OAI

/-! # Concentration of the actual sampled Cartan profiles -/

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

variable [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

/-- The actual profiles of a Borel logarithmic chain concentrate on its
initial profile under the independent probe law. No profile representative
or measurability premise is left to the application. -/
theorem cartan_actual_chain_concentration
    {K : ℕ → Type*} [∀ n, MeasurableSpace (K n)] [∀ n, Nonempty (K n)]
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
    {N : ℕ} (vertex : ∀ n, K n → Fin (N + 1) → cartanRootIdeal H)
    (hvertex : ∀ n q j,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale n)).equivFun
          (vertex n q j)‖ ≤ Real.exp (scale n * ε n))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (hvertexMeas : ∀ n j, Measurable (fun q => b₀.equivFun (vertex n q j)))
    (U : Set (Fin (finrank ℝ H) → ℝ)) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hUne : U.Nonempty)
    (hUheight : ∀ z ∈ U, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (mode : ∀ n, K n → Fin N → Fin M.letterCount)
    (t : ∀ n, K n → Fin N → ℝ) (s : Fin M.letterCount → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (htamp : ∀ j, ∀ᶠ n in atTop, ∀ q,
      |t n q j| ≤ B * Real.exp (scale n * (s (mode n q j) + ε n)))
    (hstep : ∀ n q j, F.inclusionN (F.ExpN (F.N.equiv (vertex n q j.succ))) =
      F.inclusionN (F.ExpN (F.N.equiv (vertex n q j.castSucc))) *
        Exp (t n q j • (M.letter (mode n q j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (hinterior : ∀ i, ∃ z ∈ U,
      s i < M.weight i ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z))
    (Z : Set (Fin (finrank ℝ H) → ℝ)) [CompactSpace Z] (hZU : Z ⊆ U)
    (ν : ∀ n, ProbabilityMeasure (K n))
    (j : Fin (N + 1)) {η : ℝ} (hη : 0 < η) :
    let profile : ∀ n, ((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) × K n) →
      Fin (N + 1) → C((Fin (finrank ℝ H) → ℝ), W) :=
      fun n q j => F.sampledProbeProfile hD
      (fun g => (π ((p n).val.1 g)).toAdd)
      ((hπ.comp (p n).property.1.1).continuous) (x n) (max (Real.log (scale n)) 0)
      (M.boxBasis T hunimod eW E β (scale n))
      (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
        (max (Real.log (scale n)) 0)) q.1 (vertex n q.2 j)
    Tendsto (fun n => (cellProbabilityMeasure volume
      (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)))
      (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2 :
        Measure (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)).prod (ν n : Measure (K n))
      {q | η ≤ dist ((profile n q j).restrict Z) ((profile n q 0).restrict Z)})
      atTop (𝓝 0) := by
  dsimp only
  let profile : ∀ n, ((Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) × K n) →
      Fin (N + 1) → C((Fin (finrank ℝ H) → ℝ), W) :=
    fun n q j => F.sampledProbeProfile hD
      (fun g => (π ((p n).val.1 g)).toAdd)
      ((hπ.comp (p n).property.1.1).continuous) (x n) (max (Real.log (scale n)) 0)
      (M.boxBasis T hunimod eW E β (scale n))
      (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
        (max (Real.log (scale n)) 0)) q.1 (vertex n q.2 j)
  have hp (n : ℕ) (j : Fin (N + 1)) : Measurable (fun q => profile n q j) :=
    F.measurable_sampledProbeProfile hN hD
      (fun g => (π ((p n).val.1 g)).toAdd)
      ((hπ.comp (p n).property.1.1).continuous) (x n) (max (Real.log (scale n)) 0)
      b₀ (M.boxBasis T hunimod eW E β (scale n))
      (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
        (max (Real.log (scale n)) 0))
      (fun q => vertex n q j) (hvertexMeas n j)
  let : MeasurableSpace C(Z, W) := borel _
  let : BorelSpace C(Z, W) := ⟨rfl⟩
  have hm (n : ℕ) (j : Fin (N + 1)) : Measurable (fun q =>
      dist ((profile n q j).restrict Z) ((profile n q 0).restrict Z)) := by
    have hr : Measurable (fun f : C((Fin (finrank ℝ H) → ℝ), W) => f.restrict Z) :=
      (ContinuousMap.continuous_restrict Z).measurable
    exact continuous_dist.measurable.comp ((hr.comp (hp n j)).prodMk (hr.comp (hp n 0)))
  exact M.cartan_independent_raw_chain_concentration T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
    b₀ hE hne β γ hβ hweights hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD scale hscale hmono hscale1 ε hεpos hε vertex hvertex
    rem hdim p x profile (fun _ _ _ _ _ _ => by
      simp only [profile, CartanFactorModel.sampledProbeProfile_apply])
    U hU hconn hUne hUheight σ hσ mode t s hB htamp hstep hinterior Z hZU ν hm j hη

end PolycyclicRecognition.CartanWordModel

end

end OAI
