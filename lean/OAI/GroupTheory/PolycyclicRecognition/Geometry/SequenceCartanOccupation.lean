import OAI.GroupTheory.PolycyclicRecognition.Analysis.ScaleExtension
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanOccupationInvariance
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNormalOccupation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDensityOccupation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorOccupationLimit
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairErgodic

namespace OAI

/-! # Invariance of weak limits of the actual interior Cartan chart laws -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [SecondCountableTopology G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- The actual independently sampled chart laws have invariant weak limits.
Both factor errors come from the proved Cartan slack and density estimates;
the final extension to the ambient group uses its surjective factor map. -/
theorem cartan_occupation_limit_invariant_sequence
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
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
    (K : Set (Fin (finrank ℝ H) → ℝ)) {R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ z ∈ K, ‖z‖ ≤ R)
    (hdomain : ∀ z ∈ K, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈
        (fun x => (1 - c * δ) • x) '' E)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale)
    (ε : ℕ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℕ → cartanRootIdeal H)
    (hk : ∀ᶠ r : ℕ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale r)).equivFun (k r)‖ ≤
          Real.exp (scale r * ε r))
    (ρ : (Fin (finrank ℝ H) → ℝ) → ℝ) (hcρ : Continuous ρ) (hiρ : Integrable ρ volume)
    (hpρ : ∀ z, 0 ≤ ρ z) (hmass : ∫ z, ρ z = 1) (hρK : ∀ z, z ∉ K → ρ z = 0)
    {C : Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)}
    (hC : MeasurableSet C) (hC0 : volume C ≠ 0) (hCfin : volume C ≠ ⊤)
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (ν : ProbabilityMeasure (NormalizedPair G Λ))
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop) :
    let bN := fun r => M.boxBasis T hunimod eW E β (max (scale r) 0)
    let bD := fun r => exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
      (fun i => bracketWordExponent (fun _ : I => 1) (βD.val i)) (max (Real.log (scale r)) 0)
    let chart := fun r => coordinateChartPoint (p r) (x r) F.inclusionN F.inclusionD
      (F.ExpN ∘ F.N.equiv) (F.ExpD ∘ F.D.equiv) (bN r) (bD r) (F.ExpN (F.N.equiv (k r)))
    let law := fun r => productOccupationLaw (cellProbabilityMeasure volume C hC0 hCfin)
      (densityProbabilityMeasure volume ρ hiρ hpρ hmass) (chart r)
    Tendsto law l (𝓝 ν) → SMulInvariantMeasure G (NormalizedPair G Λ) (ν : Measure _) := by
  dsimp only
  intro hlim
  let ε' := extendOnScales scale ε 0
  let k' := extendOnScales scale k 0
  let p' := extendOnScales scale p (p 0)
  let x' := extendOnScales scale x (x 0)
  have hε' : Tendsto ε' atTop (𝓝 0) := tendsto_extendOnScales hmono hε
  have hε'pos (t : ℝ) : 0 ≤ ε' t := by
    dsimp [ε', extendOnScales]
    split_ifs
    · exact hεpos _
    · exact le_rfl
  have hk' : ∀ᶠ t : ℝ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) t).equivFun (k' t)‖ ≤
          Real.exp (t * ε' t) := by
    apply eventually_extendOnScales hmono k 0
      (fun t y => ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) t).equivFun y‖ ≤
          Real.exp (t * ε' t))
    · intro t
      simp only [map_zero, norm_zero]
      exact (Real.exp_pos _).le
    · simpa only [ε', extendOnScales_apply hmono] using hk
  have hscale' : Filter.map scale l ≤ atTop := hscale.mono_left hl
  apply M.cartan_occupation_limit_invariant T F hunimod eW hExpG realize haarN haarD
    dynkinN b₀ hE hne β γ hβ hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD
    K hR hz hdomain aN hm aD hmD ε' hε'pos hε' k' hk' ρ hcρ hiρ hpρ hmass hρK
    hC hC0 hCfin p' x' ν hscale'
  apply tendsto_map'_iff.mpr
  simpa only [Function.comp_def, p', x', k', extendOnScales_apply hmono] using hlim

end PolycyclicRecognition.CartanWordModel

end

end OAI
