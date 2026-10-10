import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAllowedProfileCompactness
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborSuffixRate
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCellProbability
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxScaling
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasurableProbeProfiles

namespace OAI

/-! # Compact measurable profiles on the original two neighboring cells -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

/-- The original box bounds supply one compact family and Borel profiles
on both translated cells, after removing a finite initial segment. The
extension away from those cells is immaterial to their Haar laws. -/
theorem exists_compact_measurable_neighbor_profiles
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (scale R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (base step : ℕ → F.N.carrier)
    (hbase : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    {K : ℝ≥0} (J : ℕ → G → W) (hJ : ∀ n, LipschitzWith K (J n)) (x : ℕ → G) :
    ∃ n₀ : ℕ, ∃ S : Set C((Fin (finrank ℝ H) → ℝ), W), IsCompact S ∧
      ∃ profile : ℕ → F.N.carrier → S, (∀ n, Measurable (profile n)) ∧
      ∀ n q, q ∈ (fun v => v * base (n + n₀)) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale (n + n₀)) 1 ∪
        (fun v => v * base (n + n₀) * step (n + n₀)) ''
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale (n + n₀)) 1 → ∀ z,
        (profile n q).val z = rescaledMapProfile (J (n + n₀)) (x (n + n₀)) (F.inclusionN q)
          (max (Real.log (scale (n + n₀))) 0)
          (fun z => F.inclusionD (F.ExpD (F.D.equiv
            ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
              (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
              (max (Real.log (scale (n + n₀))) 0)).equivFun.symm z)))) z := by
  classical
  let E' := (fun w => (1 + δ) • w) '' E
  have hcost (w : M.wordList) : M.boxCost T hunimod eW E' w =
      (1 + δ) * M.boxCost T hunimod eW E w :=
    M.boxCost_image_smul T hunimod eW hE hne (by linarith) w
  have hβ' : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E') β.val := by
    refine ⟨hβ.1, ?_⟩
    intro γ hγ
    simp only [columnBasisWeight, hcost, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hβ.2 γ hγ) (by linarith)
  obtain ⟨v₀, v₁, ε, hv₀, hv₁, hε0, hε, hb⟩ :=
    M.exists_neighbor_suffix_coordinate_rate T F hunimod eW dynkinN b₀ E' β hβ'
      scale R hscale (fun n => zero_lt_one.trans_le (hscale1 n)) hR0 hR base step hbase hstep
  let s := (M.supportIn T hunimod eW).weightSupport E
  let t := fun i => (1 + δ) * s i
  have hβs : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent s w) β.val := hβ
  have hβt : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent t w) β.val := by
    have heq : M.boxCost T hunimod eW E' =
        (fun w : M.wordList => bracketWordExponent t w) := by
      funext w
      rw [hcost]
      simp only [t, bracketWordExponent_const_mul]
      rfl
    rw [← heq]
    exact hβ'
  obtain ⟨n₀, S, hS, hm⟩ := exists_compact_allowed_cartan_profiles T M F
    hExp realize haarN dynkinN haarD dynkinD X hDnil hletters bD₀ βD hβD b₀ s t
    hweights (fun i => mul_pos (by linarith) (hweights i)) β β hβs hβt
    scale hscale hscale1 ε hε J hJ x
  let r := fun n => scale (n + n₀)
  let C := fun n => (fun v => v * base (n + n₀)) ''
    M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (r n) 1 ∪
    (fun v => v * (base (n + n₀) * step (n + n₀))) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (r n) 1
  let br := fun n => exponentialRescaleBasis
    (WordBasisSelections.basis X (boundedBracketWords d) βD)
    (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (max (Real.log (r n)) 0)
  let chart := fun n z => F.inclusionD (F.ExpD (F.D.equiv ((br n).equivFun.symm z)))
  have hchart (n) : Continuous (chart n) := F.closedD.continuous.comp
    (continuous_model_exp_coordinates haarD F.ExpD F.isExpD F.D.equiv
      (F.D.tangent_nilpotent inferInstance) (br n))
  have hbound (n) :
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent t (β.val j)) (r n)).equivFun (v₀ (n + n₀))‖ ≤
          Real.exp (r n * ε (n + n₀)) ∧
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent t (β.val j)) (r n)).equivFun (v₁ (n + n₀))‖ ≤
          Real.exp (r n * ε (n + n₀)) := by
    have hb' := hb (n + n₀)
    simp only [boxBasis, hcost] at hb'
    simpa only [t, bracketWordExponent_const_mul, boxCost, s, r] using hb'
  have hmem (n q) (hq : q ∈ C n) :
      rescaledContinuousProfile (J (n + n₀)) (hJ (n + n₀)).continuous (x (n + n₀))
        (F.inclusionN q) (max (Real.log (r n)) 0) (chart n) (hchart n) ∈ S := by
    have hf (v : cartanRootIdeal H) (hv :
        ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
          (fun j => bracketWordExponent t (β.val j)) (r n)).equivFun v‖ ≤
          Real.exp (r n * ε (n + n₀)))
        (q : F.N.carrier) (hq : q ∈ (fun u => u * F.ExpN (F.N.equiv v)) ''
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (r n) 1) :
        rescaledContinuousProfile (J (n + n₀)) (hJ (n + n₀)).continuous (x (n + n₀))
          (F.inclusionN q) (max (Real.log (r n)) 0) (chart n) (hchart n) ∈ S := by
      obtain ⟨u, ⟨z, rfl, hz⟩, rfl⟩ := hq
      obtain ⟨f, hfs, he⟩ := hm n ((M.boxBasis T hunimod eW E β (r n)).equivFun z) v hz hv
      have heq : rescaledContinuousProfile (J (n + n₀)) (hJ (n + n₀)).continuous
          (x (n + n₀)) (F.inclusionN ((F.ExpN ∘ F.N.equiv) z * F.ExpN (F.N.equiv v)))
          (max (Real.log (r n)) 0) (chart n) (hchart n) = f := by
        ext w
        simpa only [boxBasis, s, boxCost, LinearEquiv.symm_apply_apply, map_mul,
          Function.comp_apply, r, chart, br, rescaledContinuousProfile, ContinuousMap.coe_mk] using (he w).symm
      exact heq ▸ hfs
    rcases hq with hq | hq
    · exact hf (v₀ (n + n₀)) (hbound n).1 q (by simpa only [hv₀] using hq)
    · exact hf (v₁ (n + n₀)) (hbound n).2 q (by simpa only [hv₁] using hq)
  have hCm (n) : MeasurableSet (C n) :=
    ((M.translated_groupBox_cell_properties T F hunimod eW haarN chartN hchartN b₀
      E β (r n) (base (n + n₀))).1).union
    (M.translated_groupBox_cell_properties T F hunimod eW haarN chartN hchartN b₀
      E β (r n) (base (n + n₀) * step (n + n₀))).1
  have hCne (n) : (C n).Nonempty := by
    apply Set.Nonempty.mono subset_union_left
    exact nonempty_of_measure_ne_zero (M.translated_groupBox_cell_properties T F
      hunimod eW haarN chartN hchartN b₀ E β (r n) (base (n + n₀))).2.1
  have hex (n) := exists_measurable_borel_sampled_profile (J (n + n₀))
    (hJ (n + n₀)).continuous (x (n + n₀)) (max (Real.log (r n)) 0) (chart n) (hchart n)
    F.inclusionN F.closedN.continuous.measurable (C n) (hCm n) (hCne n) S (hmem n)
  choose profile hp ha using hex
  refine ⟨n₀, S, hS, profile, hp, ?_⟩
  intro n q hq z
  exact ha n q (by simpa only [C, r, mul_assoc] using hq) z

end PolycyclicRecognition.CartanWordModel

end

end OAI
