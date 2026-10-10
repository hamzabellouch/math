import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanInteriorNeighbor
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfileChainConcentration
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteModeProfileChains

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

/-- Actual interior generator switches retain the starting profile on each
compact part of the open height domain, in probability. The generator may
vary with the scale and the edge of the finite chain. -/
theorem cartan_generator_chain_concentration
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
    (hvertex : ∀ j, ∀ᶠ n in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale n)).equivFun
          (vertex n j)‖ ≤ Real.exp (scale n * ε n))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    (hS : IsCompact S)
    [MetrizableSpace S] [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (profile : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) → Fin (N + 1) → S)
    (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n y j, y ∈ Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)) → ∀ z, (profile n y j).val z =
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
      {y | η ≤ dist ((profile n y j).val.restrict Z) ((profile n y 0).val.restrict Z)})
      atTop (𝓝 0) := by
  classical
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let samples : ProbabilityMeasure (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) :=
    cellProbabilityMeasure volume (Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
      (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2
  have hedge : ∀ edge : Fin N, ∀ ι : ℕ → ℕ, StrictMono ι →
      ∀ limitLaw : ProbabilityMeasure (S × S),
      Tendsto (fun n => ProbabilityMeasure.map
        (ProbabilityMeasure.map samples (profile (ι n)))
        (fun f => (f edge.castSucc, f edge.succ))) atTop (𝓝 limitLaw) →
      ∀ f ∈ (limitLaw : Measure (S × S)).support, ∀ z ∈ Z,
        f.1.val z = f.2.val z := by
    intro edge ι hι limitLaw hlim
    obtain ⟨i, φ, hφ, hmode⟩ := exists_constant_mode_subsequence (fun n => mode (ι n) edge)
    let κ := ι ∘ φ
    have hκ : StrictMono κ := hι.comp hφ
    have hκmode (n : ℕ) : mode (κ n) edge = i := hmode n
    let pair := fun n y => (profile (κ n) y edge.castSucc, profile (κ n) y edge.succ)
    have hpair (n : ℕ) : Measurable (pair n) :=
      ((measurable_pi_apply _).comp (hp (κ n))).prodMk
        ((measurable_pi_apply _).comp (hp (κ n)))
    have hpairlim : Tendsto (fun n => ProbabilityMeasure.map samples (pair n))
        atTop (𝓝 limitLaw) := by
      apply (hlim.comp hφ.tendsto_atTop).congr'
      filter_upwards [] with n
      apply Subtype.ext
      exact Measure.map_map ((measurable_pi_apply _).prodMk (measurable_pi_apply _)) (hp (κ n))
    have heq := M.cartan_interior_neighbor_profiles_eq T F hunimod eW
      hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
      b₀ hE hne β γ hβ hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD
      aN hmN aD hmD (scale ∘ κ) (hscale.comp hκ.tendsto_atTop) (hmono.comp hκ)
      (fun n => hscale1 (κ n)) (ε ∘ κ) (fun n => hεpos (κ n))
      (hε.comp hκ.tendsto_atTop)
      (fun n => vertex (κ n) edge.castSucc) (hκ.tendsto_atTop.eventually (hvertex edge.castSucc))
      (fun n => vertex (κ n) edge.succ) (hκ.tendsto_atTop.eventually (hvertex edge.succ))
      rem hdim (p ∘ κ) (x ∘ κ) S hS pair hpair
      (fun n y hy z => hactual (κ n) y edge.castSucc hy z)
      (fun n y hy z => hactual (κ n) y edge.succ hy z)
      limitLaw hpairlim U hU hconn hUne hUheight σ hσ i (fun n => t (κ n) edge) hB
      (by
        filter_upwards [hκ.tendsto_atTop.eventually (htamp edge)] with n hn
        simpa only [Function.comp_apply, hκmode] using hn)
      (by intro n; simpa only [hκmode] using hstep (κ n) edge)
      (hinterior i)
    intro f hf z hz
    exact heq f hf z (hZU hz)

  have hconcentration := profile_chain_concentration S Z N
    (fun n => ProbabilityMeasure.map samples (profile n)) hedge j hη
  have hcoord (i : Fin (N + 1)) :
      Continuous (fun f : Fin (N + 1) → S => (f i).val.restrict Z) :=
    (ContinuousMap.continuous_restrict Z).comp
      (continuous_subtype_val.comp (continuous_apply i))
  have hB : MeasurableSet {f : Fin (N + 1) → S |
      η ≤ dist ((f j).val.restrict Z) ((f 0).val.restrict Z)} :=
    (isClosed_le continuous_const ((hcoord j).dist (hcoord 0))).measurableSet
  apply hconcentration.congr'
  filter_upwards [] with n
  exact ProbabilityMeasure.map_apply' samples (hp n).aemeasurable hB

end PolycyclicRecognition.CartanWordModel

end

end OAI
