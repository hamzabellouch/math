import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanChartSlackRealization
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportedCellOccupation

namespace OAI

/-! # The normal-factor occupation estimate on the actual Cartan model -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- A fixed normal-factor translation has vanishing error for the actual
chart law, including an enlarged suffix and a density supported in the
interior height region. No invariance of the limiting measure is assumed. -/
theorem cartan_normal_occupation_error_tendsto_zero
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
    (X : I → H) (S : Finset (FreeMagma I)) (βD : WordBasisSelections X S)
    (K : Set (Fin (finrank ℝ H) → ℝ)) {R : ℝ} (hR : 0 ≤ R)
    (hz : ∀ z ∈ K, ‖z‖ ≤ R)
    (hdomain : ∀ z ∈ K, eW (heightProjection T.character
      ((WordBasisSelections.basis X S βD).equivFun.symm z : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈
        (fun x => (1 - c * δ) • x) '' E)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hm : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    (ε : ℝ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℝ → cartanRootIdeal H)
    (hk : ∀ᶠ r : ℝ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) r).equivFun (k r)‖ ≤
          Real.exp (r * ε r))
    (ρ : (Fin (finrank ℝ H) → ℝ) → ℝ) (hiρ : Integrable ρ volume)
    (hpρ : ∀ z, 0 ≤ ρ z) (hmass : ∫ z, ρ z = 1) (hρK : ∀ z, z ∉ K → ρ z = 0)
    {C : Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)}
    (hC : MeasurableSet C) (hC0 : volume C ≠ 0) (hCfin : volume C ≠ ⊤)
    (p : ℝ → NormalizedPair G Λ) (x : ℝ → G) (v : cartanRootIdeal H)
    (f : C(NormalizedPair G Λ, ℝ)) :
    let bN := fun r => M.boxBasis T hunimod eW E β (max r 0)
    let bD := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S βD)
      (fun i => bracketWordExponent (fun _ : I => 1) (βD.val i)) (max (Real.log r) 0)
    let chart := fun r => coordinateChartPoint (p r) (x r) F.inclusionN F.inclusionD
      (F.ExpN ∘ F.N.equiv) (F.ExpD ∘ F.D.equiv) (bN r) (bD r) (F.ExpN (F.N.equiv (k r)))
    let law := fun r => productOccupationLaw (cellProbabilityMeasure volume C hC0 hCfin)
      (densityProbabilityMeasure volume ρ hiρ hpρ hmass) (chart r)
    Tendsto (fun r : ℝ =>
      (∫ y, f ((F.inclusionN (F.ExpN (F.N.equiv v)))⁻¹ • y) ∂(law r : Measure _)) -
        ∫ y, f y ∂(law r : Measure _)) atTop (𝓝 0) := by
  let bN := fun r => M.boxBasis T hunimod eW E β (max r 0)
  let bD := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S βD)
    (fun i => bracketWordExponent (fun _ : I => 1) (βD.val i)) (max (Real.log r) 0)
  let chart := fun r => coordinateChartPoint (p r) (x r) F.inclusionN F.inclusionD
    (F.ExpN ∘ F.N.equiv) (F.ExpD ∘ F.D.equiv) (bN r) (bD r) (F.ExpN (F.N.equiv (k r)))
  let q := fun r z => dynkinProduct aN (basisBracket (bN r))
    (dynkinProduct aN (basisBracket (bN r)) ((bN r).equivFun (k r))
      ((bN r).equivFun (cartanIdealAdjointAutomorphism T H ((bD r).equivFun.symm z) v)))
    (-((bN r).equivFun (k r)))
  have hq : TendstoUniformly (fun r (z : K) => q r z) (fun _ => 0) atTop := by
    have hh := M.chart_suffix_conjugation_of_published_realization T F hunimod eW
      hExpG realize haarN b₀ hE hne β γ hβ hδ hc hhi ht hcost hgap X S βD
      (fun z : K => z.val) hR (fun z => hz z z.property) (fun z => hdomain z z.property)
      aN hm ε hεpos hε k hk v
    apply (tendstoUniformly_congr ?_).mp hh
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    funext z
    dsimp only [q, bN, bD]
    rw [max_eq_left (by linarith : 0 ≤ r), max_eq_left (Real.log_nonneg hr)]
    simp only [bracketWordExponent_one]
  obtain ⟨D, hD, hbracket⟩ := exists_uniform_rescaled_structureConstant_bound M.letter M.bound_zero b₀
  have hb (r : ℝ) : ‖basisBracket (bN r)‖ ≤
      (finrank ℝ (cartanRootIdeal H) : ℝ) ^ 2 * D :=
    norm_basisBracket_le _ hD (hbracket ((M.supportIn T hunimod eW).weightSupport E)
      β hβ (max r 0) (le_max_right _ _))
  have hmeas (r : ℝ) : Measurable (chart r) := by
    apply Continuous.measurable
    apply continuous_coordinateChartPoint
    · exact F.closedN.continuous.comp (continuous_model_exp_coordinates haarN F.ExpN F.isExpN
        F.N.equiv (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T)) (bN r))
    · exact F.closedD.continuous.comp (continuous_model_exp_coordinates haarD F.ExpD F.isExpD
        F.D.equiv (F.D.tangent_nilpotent inferInstance) (bD r))
  apply supported_model_cell_occupation_error_tendsto_zero haarN F.ExpN F.isExpN F.N.equiv
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T)) bN aN hm hb q
    (densityProbabilityMeasure volume ρ hiρ hpρ hmass) K
    (ae_mem_densityProbabilityMeasure volume ρ hiρ hpρ hmass K hρK) hq hC hC0 hCfin
    chart hmeas (F.inclusionN (F.ExpN (F.N.equiv v)))⁻¹ _ f
  intro r u z
  exact coordinateChartPoint_normal_of_exponential_action (p r) (x r) F.inclusionN F.inclusionD
    F.action F.conjugation (F.ExpN ∘ F.N.equiv) (F.ExpD ∘ F.D.equiv)
    (fun y => by simp [F.isExpN.map_neg]) (fun h w => cartanIdealAdjointAutomorphism T H h w)
    (cartan_action_exp_of_published_realization T M F hExpG realize haarN haarD dynkinN)
    (bN r) (bD r) (k r) v aN (model_binary_dynkin F.N.equiv F.ExpN aN hm) (u, z)

end PolycyclicRecognition.CartanWordModel

end

end OAI
