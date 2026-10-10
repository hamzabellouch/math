import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProfileRestriction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanOccupation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanStationaryTemplateIncrement
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FlowSupportedProfileIncrement
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoordinateFlowProfileIdentity
import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationaryIntegralMicrosteps
import Mathlib.Analysis.Convex.Topology

namespace OAI

/-! # Convex increments of Cartan profiles

The invariant occupation measure, stationary estimate, coordinate flow and
exact increment identity give profile increment bounds under compactness and
interior-segment hypotheses.
-/

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

theorem cartan_profile_increment_mem_template_sequence
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
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale)
    (ε : ℕ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℕ → cartanRootIdeal H)
    (hk : ∀ᶠ r : ℕ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale r)).equivFun (k r)‖ ≤
          Real.exp (scale r * ε r))
    {C : Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)}
    (hC : MeasurableSet C) (hC0 : volume C ≠ 0) (hCfin : volume C ≠ ⊤)
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G) (v : H) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let logscale := fun r : ℕ => max (Real.log (scale r)) 0
    let bN := fun r => M.boxBasis T hunimod eW E β (max (scale r) 0)
    let bD := fun r => exponentialRescaleBasis b cost (logscale r)
    let Flim := dynkinFlowMap aD (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v)
    ∀ (S : Set C((Fin (finrank ℝ H) → ℝ), W)) (_hS : IsCompact S)
      [MeasurableSpace S] [BorelSpace S]
      (profile : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) → S),
      (∀ r, Measurable (profile r)) →
      (∀ r y, y ∈ C → ∀ z, (profile r y).val z =
        rescaledMapProfile (fun g => (π ((p r).val.1 g)).toAdd) (x r)
          (F.inclusionN (F.ExpN (F.N.equiv ((bN r).equivFun.symm y))) *
            F.inclusionN (F.ExpN (F.N.equiv (k r))))
          (logscale r) (fun z => F.inclusionD (F.ExpD (F.D.equiv ((bD r).equivFun.symm z)))) z) →
      ∀ (ν : ProbabilityMeasure S),
      Tendsto (fun r => ProbabilityMeasure.map (cellProbabilityMeasure volume C hC0 hCfin)
        (profile r)) atTop (𝓝 ν) →
      ∀ {U : Set (Fin (finrank ℝ H) → ℝ)}, IsOpen U →
      (∀ z ∈ U, eW (heightProjection T.character
        (b.equivFun.symm z : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈
          (fun w => (1 - c * δ) • w) '' E) →
      ∀ (z : Fin (finrank ℝ H) → ℝ) {T₀ : ℝ}, 0 < T₀ →
      (∀ t ∈ Icc 0 T₀, Flim (z, t) ∈ U) →
      ∀ {f : S}, f ∈ (ν : Measure S).support →
      T₀⁻¹ • (f.val (Flim (z, T₀)) - f.val z) ∈
        convexHull ℝ (Set.range (fun A : templateSymmetryGroup (M.supportIn T hunimod eW) =>
          A.val (eW (heightProjection T.character v)))) := by
  dsimp only
  intro S hS _ _ profile hprofile hactual ν hν U hU hUheight z T₀ hT hseg f hf
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
  let logscale := fun r : ℕ => max (Real.log (scale r)) 0
  let bN := fun r => M.boxBasis T hunimod eW E β (max (scale r) 0)
  let bD := fun r => exponentialRescaleBasis b cost (logscale r)
  let Fs := fun r => dynkinFlowMap aD (basisBracket (bD r))
    ((bD r).equivFun (Real.exp (logscale r) • v))
  let Flim := dynkinFlowMap aD (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v)
  let chart := fun r => coordinateChartPoint (p r) (x r) F.inclusionN F.inclusionD
    (F.ExpN ∘ F.N.equiv) (F.ExpD ∘ F.D.equiv) (bN r) (bD r) (F.ExpN (F.N.equiv (k r)))
  let ray := fun t : ℝ => Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let B := Set.range (fun A : templateSymmetryGroup (M.supportIn T hunimod eW) =>
    A.val (eW (heightProjection T.character v)))
  have hlogscale : Tendsto logscale atTop atTop :=
    tendsto_atTop_mono (fun r => le_max_left (Real.log (scale r)) 0)
      (Real.tendsto_log_atTop.comp hscale)
  have hweight := maximizing_word_basis_bracket_weight X hDnil bD₀ (fun _ => 1) βD hβD
  have hlength (w : FreeMagma I) : 1 ≤ bracketWordLength w := by
    induction w using FreeMagma.rec with
    | of j => simp [bracketWordLength]
    | mul u w hu hw => simp only [bracketWordLength]; omega
  have hvelocity : ∀ j, b.repr v j ≠ 0 → (1 : ℝ) ≤ cost j := by
    intro j _
    dsimp only [cost]
    rw [bracketWordExponent_one]
    exact_mod_cast hlength (βD.val j)
  have hflow : Tendsto Fs atTop (𝓝 Flim) :=
    (rescaled_horizontal_flow_tendsto aD b cost hweight v hvelocity).comp hlogscale
  have hchart (r : ℕ) : Measurable (chart r) := by
    apply Continuous.measurable
    apply continuous_coordinateChartPoint
    · exact F.closedN.continuous.comp (continuous_model_exp_coordinates haarN F.ExpN F.isExpN
        F.N.equiv (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T)) (bN r))
    · exact F.closedD.continuous.comp (continuous_model_exp_coordinates haarD F.ExpD F.isExpD
        F.D.equiv (F.D.tangent_nilpotent inferInstance) (bD r))
  have hB : IsCompact B := (Set.toFinite B).isCompact
  apply supported_profile_increment_of_flow S hS π hπ
    (fun _ => cellProbabilityMeasure volume C hC0 hCfin) profile hprofile ν hν volume
    Fs Flim hflow
    (fun r t => measurePreserving_model_horizontal_flow haarD F.ExpD F.isExpD F.D.equiv
      (F.D.tangent_nilpotent inferInstance) (bD r) aD hmD (Real.exp (logscale r)) t v)
    chart hchart ray
    (continuous_exp_line_of_published_realization T Exp hExp realize v)
    (by simp [ray, hExp.map_zero]) (fun s t => hExp.map_add_smul v s t)
    (fun r => Real.exp (logscale r)) (Real.tendsto_exp_atTop.comp hlogscale) hT
    ?_ ?_ hU z hseg ?_ hB ⟨1, rfl⟩ ((Set.toFinite B).isClosed_convexHull ℝ) ?_ hf
  · intro r y w t
    have he : F.inclusionD (F.ExpD (F.D.equiv ((Real.exp (logscale r) * t) • v))) =
        ray (Real.exp (logscale r) * t) := by
      rw [F.compatibleD]
      rfl
    simpa only [Function.comp_apply, he] using coordinateChartPoint_horizontal_flow (p r) (x r)
      F.inclusionN F.inclusionD (F.ExpN ∘ F.N.equiv) (F.ExpD ∘ F.D.equiv)
      (bN r) (bD r) (F.ExpN (F.N.equiv (k r))) aD
      (model_binary_dynkin F.D.equiv F.ExpD aD hmD) v (Real.exp (logscale r)) t (y, w)
  · intro r
    filter_upwards [ae_mem_cellProbabilityMeasure volume C hC hC0 hCfin] with y hy
    intro w
    simp only [hactual r y hy]
    have he : F.inclusionD (F.ExpD (F.D.equiv ((Real.exp (logscale r) * T₀) • v))) =
        ray (Real.exp (logscale r) * T₀) := by
      rw [F.compatibleD]
      rfl
    simpa only [Function.comp_apply, he] using coordinate_rescaled_profile_increment π (p r) (x r)
      F.inclusionN F.inclusionD (F.ExpN ∘ F.N.equiv) (F.ExpD ∘ F.D.equiv)
      (bN r) (bD r) (F.ExpN (F.N.equiv (k r))) aD
      (model_binary_dynkin F.D.equiv F.ExpD aD hmD) v (logscale r) T₀ y w
  · intro ρ hiρ hpρ hmass hcomp hsupport u hu μ hμ
    obtain ⟨R, hR, hbound⟩ := hcomp.isBounded.exists_pos_norm_le
    exact M.cartan_occupation_limit_invariant_sequence T F hunimod eW hExp realize haarN haarD dynkinN
      b₀ hE hne β γ hβ hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD
      (tsupport ρ) hR.le hbound (fun w hw => hUheight w (hsupport hw)) aN hmN aD hmD
      scale hscale hmono ε hεpos hε k hk ρ ρ.continuous hiρ hpρ hmass
      (fun w hw => image_eq_zero_of_notMem_tsupport hw) hC hC0 hCfin p x μ hu hμ
  · intro μ hμ
    let := hμ
    obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
      (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
    obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
      (F.D.tangent_nilpotent inferInstance)
    apply stationary_integral_microsteps (Λ := Λ) π hπ.continuous ray B (μ : Measure _)
    exact M.increments_tendsto_template_labels_of_invariant_probability T F hunimod eW π hπExp
      chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD hExp realize m
      (μ : Measure _) hdec hvan hΛ hπ b₀
      (fun d => cartan_action_eq_adjoint_of_published_realization T M F hExp realize
        (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective)
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) dynkinN d)
      hpath v

end PolycyclicRecognition.CartanWordModel

end

end OAI
