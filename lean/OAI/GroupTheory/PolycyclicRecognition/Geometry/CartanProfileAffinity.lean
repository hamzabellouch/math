import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProfileSegmentVolume
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanProfileIncrement
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportedCellLipschitz
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfileAffinityCriterion

namespace OAI

/-! # Affinity of the actual supported Cartan profiles -/

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

theorem cartan_supported_profile_affine_sequence
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
    (profile : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) → S)
    (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n y, y ∈ Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)) → ∀ z, (profile n y).val z =
      rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
        (F.inclusionN (F.ExpN (F.N.equiv
          ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y))) *
            F.inclusionN (F.ExpN (F.N.equiv (k n))))
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure volume (Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
        (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
      (profile n)) atTop (𝓝 ν))
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
  classical
  let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
  let br := gradedCoordinateBracket bD cost
  let P := M.supportIn T hunimod eW
  let h : H →ₗ[ℝ] W := eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)
  let pH := (h.comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
  let D := ((gradedGeneratorLinearMap bD cost 1).comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
  have hh (v w : H) : h ⁅v, w⁆ = 0 := by
    change eW (heightProjection T.character (⁅v, w⁆ : H)) = 0
    rw [LieSubalgebra.coe_bracket, heightProjection_lie_eq_zero T.character T.character_lie,
      map_zero]
  have hweight := maximizing_word_basis_bracket_weight X hDnil bD₀ (fun _ => 1) βD hβD
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  let ExpH := fun v : H => F.inclusionD (F.ExpD (F.D.equiv v))
  have hExpH (v : H) : ExpH v = Exp v := F.compatibleD v
  have hinj : Function.Injective ExpH := F.closedD.injective.comp
    (((funext hchartD ▸ chartD.bijective).comp F.D.equiv.bijective).injective)
  have hzero : ExpH 0 = 1 := by simp [ExpH, F.isExpD.map_zero]
  have hneg (v : H) : ExpH (-v) = (ExpH v)⁻¹ := by simp [ExpH, F.isExpD.map_neg]
  have hadd (v : H) (s t : ℝ) : ExpH ((s + t) • v) = ExpH (s • v) * ExpH (t • v) := by
    simp only [ExpH, map_smul, F.isExpD.map_add_smul, map_mul]
  have hmul (v w : H) : ExpH (finiteDynkinPolynomial aD ![v, w]) = ExpH v * ExpH w :=
    (congrArg F.inclusionD (model_binary_dynkin F.D.equiv F.ExpD aD hmD v w)).trans
      (map_mul F.inclusionD _ _)
  have hπH (v : H) : (π (ExpH v)).toAdd = h v := by
    rw [hExpH, hπExp]
    rfl
  have hg : PolynomialGroupLaws (dynkinProduct aD br) :=
    gradedCoordinateBracket_groupLaws bD cost hweight ExpH hinj hzero hneg hadd aD hmul
  have hconj := cartan_graded_conjugation T F hExp realize haarD bD cost hweight aD hmD
  have hheight (v w) : pH (dynkinProduct aD br v w) = pH v + pH w :=
    gradedWordChartProduct_height X (boundedBracketWords d) βD h hh ExpH π hπH aD hmul hweight v w
  let π₀ := polynomialCoordinateHeightHom (dynkinProduct aD br) hg pH hheight
  have hDheight (v : Fin (finrank ℝ H) → ℝ) : pH (D v) = h (bD.equivFun.symm v) :=
    gradedGenerator_word_height X (boundedBracketWords d) βD h hh (bD.equivFun.symm v)
  have hsurj : Function.Surjective (pH.comp D) := by
    intro w
    obtain ⟨v, hv⟩ := (eW.surjective.comp (cartan_height_surjective T H)) w
    refine ⟨bD.equivFun v, ?_⟩
    change pH (D (bD.equivFun v)) = w
    rw [hDheight, bD.equivFun.symm_apply_apply]
    exact hv
  let e := PolynomialCoordinateGroup.expHomeomorph (dynkinProduct aD br) hg
  let μ := Measure.map e volume
  have hmeasure := polynomialCoordinate_haar_of_right_translations (dynkinProduct aD br) hg
    (continuous_dynkinProduct aD (fun _ => br) Prod.fst Prod.snd
      continuous_const continuous_fst continuous_snd)
    (fun q => measurePreserving_model_graded_dynkin_right F.D.equiv haarD F.ExpD F.isExpD
      inferInstance bD cost hweight aD hmD q)
  have hhaar : μ.IsHaarMeasure := hmeasure.1
  have hright : μ.IsMulRightInvariant := hmeasure.2
  let : μ.IsHaarMeasure := hhaar
  let : μ.IsMulRightInvariant := hright
  let L := templateSymmetryGroup P
  let : Fintype L := Fintype.ofFinite L
  let : MeasurableSpace L := ⊤
  have hweights (i : Fin M.letterCount) : P.weight i ≠ 0 := by
    intro hz
    apply M.weight_nonzero i
    funext v
    have hv := congrArg (fun q : W →ₗ[ℝ] ℝ => q (eW (heightProjection T.character v))) hz
    simpa only [P, supportIn, SupportDatum.transport_weight_apply, supportDatum_weight,
      eW.symm_apply_apply, cartanHeightWeight_projection, LinearMap.zero_apply,
      Pi.zero_apply] using hv
  let logscale := fun n => max (Real.log (scale n)) 0
  have hlogscale : Tendsto logscale atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left _ _) (Real.tendsto_log_atTop.comp hscale)
  let samples : ProbabilityMeasure (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) := cellProbabilityMeasure volume
    (Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
    (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2
  let J := fun n (_ : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) (g : G) =>
    (π ((p n).val.1 g)).toAdd
  have hJ (n : ℕ) (y : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) :
      LipschitzWith (Kπ * Λ) (J n y) := hπ.comp (p n).property.1.1
  let suffixN : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) → G := fun n y => F.inclusionN (F.ExpN (F.N.equiv
    ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y))) *
      F.inclusionN (F.ExpN (F.N.equiv (k n)))
  have hlip := lipschitz_supported_cartan_profiles_on T F hExp realize X hDnil bD₀ βD hβD
    aD hmD logscale hlogscale J hJ (fun n _ => x n) suffixN S hS (fun _ => samples)
    profile hp ν hν (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))) measurableSet_Icc
    (fun _ => ae_mem_cellProbabilityMeasure volume _ measurableSet_Icc _ _) hactual
  choose C hC using hlip
  have hDX (i : I) : D (bD.equivFun (X i)) = gradedGenerator bD cost 1 (X i) := by
    change gradedGenerator bD cost 1 (bD.equivFun.symm (bD.equivFun (X i))) = _
    rw [bD.equivFun.symm_apply_apply]
  have hwords (j : Fin (finrank ℝ H)) :
      evalBilinearWord br (fun i => D (bD.equivFun (X i))) (βD.val j) =
        Pi.basisFun ℝ (Fin (finrank ℝ H)) j := by
    simp only [hDX]
    simpa only [Pi.basisFun_apply] using
      graded_generators_word_normalization X hDnil hDletters bD₀ (fun _ => 1) βD hβD j
  intro f hf
  apply affine_profile_of_segment_inequalities aD br
    (isLieBracket_gradedCoordinateBracket bD cost hweight) hg hconj D (Pi.basisFun ℝ (Fin (finrank ℝ H)))
    (fun i => bD.equivFun (X i)) (Pi.basisFun ℝ (Fin (finrank ℝ H)))
    (fun j => (βD.val j : FreeMagma I)) hwords
    μ U hU hconn hUne f.val f.val.continuous π₀ pH hsurj (fun _ => rfl) P hweights σ hσ
    (fun A : L => A) (fun v => C (bD.equivFun.symm v))
    (fun v z => (hC (bD.equivFun.symm v) f hf z).lipschitzOnWith) ?_
  intro v₀ T₀ hT z hseg
  let v := bD.equivFun.symm v₀
  have hseg' : ∀ t ∈ Icc 0 T₀,
      dynkinFlowMap aD br (gradedGenerator bD cost 1 v) (z, t) ∈ U := hseg
  rw [hDheight]
  constructor
  · apply M.cartan_profile_increment_mem_template_sequence T F hunimod eW
      hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
      b₀ hE hne β γ hβ hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD
      aN hmN aD hmD scale hscale hmono ε hεpos hε k hk
      (C := Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
      (measurableSet_Icc) (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2
      p x v S hS profile hp ?_ ν hν hU hUheight z hT hseg' hf
    intro n y hy z
    simpa only [max_eq_left ((hscale1 n).trans' zero_le_one)] using hactual n y hy z
  · exact M.cartan_profile_segment_volume_sequence T F hunimod eW
      hExp realize haarN haarD dynkinN dynkinD π hπExp hΛ hπ hpath b₀ hE hne β hβ
      hδ hc hhi ht hcost hgap X hDnil bD₀ βD hβD aN hmN aD hmD
      scale hscale hmono hscale1 ε hεpos hε k hk rem hdim p x S profile hp hactual
      ν hν v z T₀ hT U hU hUheight hseg' f hf

end PolycyclicRecognition.CartanWordModel

end

end OAI
