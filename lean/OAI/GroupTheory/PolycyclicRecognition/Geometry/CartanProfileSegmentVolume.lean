import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxScaling
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSegmentCellPacking
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGoodCellLegs
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRecurrenceCells
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxSchemes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FlowSegmentImages
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubsequences
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateSupportOrder
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # The volume inequality for supported limiting Cartan chart profiles -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology NNReal ENNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0}

/-- The fixed submersive word is selected before good profiles are retained.
Actual interval laws and a fixed enlarged Haar box then supply recurrence,
and the physical segment legs yield the support-volume inequality. -/
theorem cartan_profile_segment_volume_sequence
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
    (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
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
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (profile : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) → S)
    (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n y, y ∈ Icc
      (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)) →
      ∀ z, (profile n y).val z =
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
      (profile n)) atTop (𝓝 ν)) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let P := M.supportIn T hunimod eW
    ∀ (v : H) (z : Fin (finrank ℝ H) → ℝ) (T₀ : ℝ), 0 < T₀ →
      let flow := dynkinFlowMap aD (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v)
      ∀ (U : Set (Fin (finrank ℝ H) → ℝ)), IsOpen U →
        (∀ y ∈ U, eW (heightProjection T.character (b.equivFun.symm y :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' E) →
        (∀ t ∈ Icc 0 T₀, flow (z, t) ∈ U) →
        ∀ f : S, f ∈ (ν : Measure S).support →
          T₀ * P.segmentSupport (eW (heightProjection T.character v)) ≤
            P.templateSupport ((fun t => f.val (flow (z, t))) '' Icc 0 T₀) := by
  dsimp only
  intro v z T₀ hT₀ U hU hUheight hseg f hf
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
  let flow := dynkinFlowMap aD (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v)
  let P := M.supportIn T hunimod eW
  let h : H →ₗ[ℝ] W := eW.toLinearMap.comp ((heightProjection T.character).comp H.incl.toLinearMap)
  let source := segment ℝ (h (b.equivFun.symm z)) (h (b.equivFun.symm z) + T₀ • h v)
  have hbr (u v : H) : h ⁅u, v⁆ = 0 := by
    change eW (heightProjection T.character ⁅(u : GroupLieAlgebra (𝓘(ℝ, EG)) G), v⁆) = 0
    rw [T.height_lie, map_zero]
  have hweight := maximizing_word_basis_bracket_weight X hDnil bD₀ (fun _ => 1) βD hβD
  have hExpHeight (u : H) :
      ((π.comp F.inclusionD) ((F.ExpD ∘ F.D.equiv) u)).toAdd = h u := by
    simp only [MonoidHom.comp_apply, Function.comp_apply, F.compatibleD, hπExp]
    rfl
  have himage := gradedWordChartFlow_height_image X (boundedBracketWords d) βD h hbr
    (F.ExpD ∘ F.D.equiv) (π.comp F.inclusionD) hExpHeight aD
    (model_binary_dynkin F.D.equiv F.ExpD aD hmD) v z hT₀ hweight
  change (fun y => h (b.equivFun.symm y)) '' ((fun t => flow (z, t)) '' Icc 0 T₀) = source at himage
  have hsourceSub : source ⊆ (fun w => (1 - c * δ) • w) '' E := by
    rw [← himage]
    rintro w ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    exact hUheight _ (hseg t ht)
  have hq (i : Fin M.letterCount) :
      P.weightSupport source i ≤ (1 - c * δ) * P.weightSupport E i := by
    have hh := P.weightSupport_mono (isCompact_segment_real _ _) ⟨_, left_mem_segment ℝ _ _⟩
      (hE.image (continuous_const.smul continuous_id)) hsourceSub i
    change P.weightSupport source i ≤ P.weightSupport ((fun w : W => (1 - c * δ) • w) '' E) i at hh
    exact hh.trans_eq (P.weightSupport_image_smul hE hne ht i)
  obtain ⟨γ, hγ, _⟩ := M.exists_maximizing_box_basis T hunimod eW b₀ source
  obtain ⟨C₀, hC₀, hparams⟩ := M.exists_box_normalized_bound T F hunimod eW hExp realize haarN
    b₀ aN hmN source γ hγ
  let parameters := normalizedExponentialParameters aN
    (fun i => (γ.val i : FreeMagma (Fin M.letterCount))) (fun i => Pi.single i (1 : ℝ)) C₀
  let law := fun n => rescaledLieData M.letter M.wordList γ (P.weightSupport source) (scale n)
  have hlaw (n : ℕ) : law n ∈ parameters := hparams (scale n) (zero_le_one.trans (hscale1 n))
  obtain ⟨q, hqmem, u, hu, hlim, m, letters, t₀, _, honto⟩ :=
    exists_submersive_scheme_of_normalized_sequence aN
      (fun i => (γ.val i : FreeMagma (Fin M.letterCount))) C₀ law hlaw
  let ρ := max 1 ‖t₀‖
  have hρ : 1 ≤ ρ := le_max_left _ _
  have ht₀ : ‖t₀‖ ≤ ρ := le_max_right _ _
  have hru : Tendsto (scale ∘ u) atTop atTop := hscale.comp hu.tendsto_atTop
  have hku := hu.tendsto_atTop.eventually hk
  have hcells := M.exists_interval_recurrence_cells_sequence T F hunimod eW hExp realize
    haarN dynkinN b₀ E β (P.weightSupport source) hβ hδ hc hhi (zero_le_one.trans hρ)
    hcost hgap hq (scale ∘ u) hru (hmono.comp hu) (ε ∘ u)
    (fun n => hεpos (u n)) (hε.comp hu.tendsto_atTop) (k ∘ u) hku letters
  dsimp only at hcells
  rcases hcells with ⟨D₀, hD₀, hmass, hratio, hcontain⟩
  obtain ⟨w, hw, hwgood⟩ := extraction_of_eventually_atTop hcontain
  let index := u ∘ w
  have hindex := hu.comp hw
  have hr : Tendsto (scale ∘ index) atTop atTop := hscale.comp hindex.tendsto_atTop
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
  have hcube := coordinate_cube_mass (n := finrank ℝ (cartanRootIdeal H)) zero_lt_one
  have hg : Continuous (fun t => f.val (flow (z, t))) :=
    f.val.continuous.comp (flow.continuous.comp (continuous_const.prodMk continuous_id))
  have hgood := M.exists_good_cartan_cell_legs_sequence T F hunimod eW haarN chartN hchartN
    b₀ E β (scale ∘ index) hr (k ∘ index) X hDnil bD₀ βD hβD aD hmD
    (fun n g => (π ((p (index n)).val.1 g)).toAdd) (x ∘ index)
    cube measurableSet_Icc hcube.1 hcube.2 S (fun n => profile (index n))
    (fun n => hp (index n)) ν (hν.comp hindex.tendsto_atTop)
    v z T₀ U hU hseg (fun n y hy z => hactual (index n) y hy z) hf
  dsimp only at hgood
  rcases hgood with ⟨A, ζ, hA, hAQ, hApos, hζpos, hζ, hAlower, hlegs⟩
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let Q := fun n => (fun y => y * F.ExpN (F.N.equiv (k (index n)))) ''
    M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale (index n)) 1
  let R := fun n => (fun y => y * F.ExpN (F.N.equiv (k (index n)))) ''
    M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale (index n)) D₀
  have hQ (n : ℕ) : Q n =
      (fun y => F.ExpN (F.N.equiv ((M.boxBasis T hunimod eW E β (scale (index n))).equivFun.symm y)) *
        F.ExpN (F.N.equiv (k (index n)))) '' cube := by
    dsimp only [Q, groupBox]
    rw [exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one, ← image_comp]
    rfl
  let sample := fun n j t => rootIntervalSample (F.ExpN ∘ F.N.equiv) letters M.letter
    (P.weightSupport source) (scale (index n)) j t
  let σ := fun n j => rootIntervalLaw (F.ExpN ∘ F.N.equiv) letters M.letter
    (P.weightSupport source) (scale (index n)) ρ j
  have hcont (v : cartanRootIdeal H) : Continuous (fun t : ℝ => (F.ExpN ∘ F.N.equiv) (t • v)) := by
    have hb := continuous_model_exp_coordinates haarN F.ExpN F.isExpN F.N.equiv
      (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T)) b₀
    have he (t : ℝ) : (F.ExpN ∘ F.N.equiv) (t • v) =
        F.ExpN (F.N.equiv (b₀.equivFun.symm (t • b₀.equivFun v))) := by simp
    simp_rw [he]
    exact hb.comp (continuous_id.smul continuous_const)
  let : ∀ n j, IsProbabilityMeasure (σ n j) := fun n j =>
    rootIntervalLaw_isProbability _ letters M.letter _ _ (zero_lt_one.trans_le hρ) j
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haarN F.N.equiv
    (cartanRootIdeal_nilpotent H T) F.ExpN F.isExpN b₀
  have hpack := M.templateSupport_le_of_recurrent_segment_cells_sequence T F hunimod eW π hπExp
    dynkinN dynkinD haarN haarD hExp realize (scale ∘ index) hr
    (fun n => hscale1 (index n)) b₀ X (boundedBracketWords d) βD z v hT₀ source rfl γ hγ
    (x ∘ index) A Q (fun n j => rootIntervalSupport (F.ExpN ∘ F.N.equiv) letters M.letter
      (P.weightSupport source) (scale (index n)) ρ j) (fun n _ => R n) (fun _ _ => D₀ ^ finrank ℝ (cartanRootIdeal H))
    μ (p ∘ index) hΛ hpath hπ aN hmN letters sample
    (fun n j t s => rootIntervalSample_sub _
      (fun v => by simp [F.isExpN.map_neg])
      (fun v t s => by simpa only [Function.comp_apply, map_smul] using F.isExpN.map_add_smul (F.N.equiv v) t s)
      letters M.letter _ _ j t s)
    (fun n j t => rootIntervalSample_letter _ letters M.letter _ _ j t)
    parameters (isCompact_normalizedExponentialParameters _ _ _ _)
    (fun n => hlaw (index n)) q hqmem (hlim.comp hw.tendsto_atTop)
    rem hdim ρ hρ t₀ ht₀ honto σ
    (fun n j => measurePreserving_rootIntervalSample _ hcont letters M.letter _ _ _ j)
    (fun n => (hmass (w n)).2.1) (fun n => (hmass (w n)).1)
    (fun n j => rootIntervalLaw_ae_mem_support _ hcont letters M.letter _ _ _ j)
    (fun n j => (hmass (w n)).2.2.2) (fun n j => (hmass (w n)).2.2.1)
    (fun n j => hwgood n j) (fun n j => pow_pos (zero_lt_one.trans_le hD₀) _)
    (fun n j => le_of_eq (hratio (w n))) hA
    (fun n => by simpa only [hQ n, Function.comp_apply] using hAQ n) hApos
    (by simpa only [hQ, Function.comp_apply, μ] using hAlower)
    (fun j _ => sequence_subexponential_upper_const hr _) (fun t => f.val (flow (z, t))) hg
    (fun n => (π ((p (index n)).val.1 (x (index n)))).toAdd) ζ hζ hlegs
  have hsourceExp : P.templateSupport source = T₀ * P.segmentSupport (h v) :=
    P.templateSupport_affine_segment _ _ hT₀.le
  rw [hsourceExp] at hpack
  exact hpack

end PolycyclicRecognition.CartanWordModel

end

end OAI
