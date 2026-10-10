import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanChainCompactProfiles
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxCompact

namespace OAI

/-! # Profiles fixed before the small enlargement is chosen -/

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

/-- Choose a compact family and one Borel profile map for every allowed
suffix in a fixed larger box. No particular chain or smaller enlargement
is chosen until after this family has been fixed. -/
theorem exists_compact_measurable_box_profiles
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
    {K : ℝ≥0} (J : ℕ → G → W) (hJ : ∀ n, LipschitzWith K (J n)) (x : ℕ → G) :
    ∃ n₀ : ℕ, ∃ S : Set C((Fin (finrank ℝ H) → ℝ), W), IsCompact S ∧
      ∃ profile : ℕ → F.N.carrier → S, (∀ n, Measurable (profile n)) ∧
      ∀ n k, k ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        ((fun w => (1 + δ) • w) '' E) β (scale (n + n₀)) (R (n + n₀)) →
      ∀ q, q ∈ (fun v => v * k) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale (n + n₀)) 1 → ∀ z,
        (profile n q).val z = rescaledMapProfile (J (n + n₀)) (x (n + n₀)) (F.inclusionN q)
          (max (Real.log (scale (n + n₀))) 0)
          (fun z => F.inclusionD (F.ExpD (F.D.equiv
            ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
              (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
              (max (Real.log (scale (n + n₀))) 0)).equivFun.symm z)))) z := by
  classical
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let E' := (fun w => (1 + δ) • w) '' E
  let s := (M.supportIn T hunimod eW).weightSupport E
  let t := fun i => (1 + δ) * s i
  have hcost (w : M.wordList) : M.boxCost T hunimod eW E' w =
      (1 + δ) * M.boxCost T hunimod eW E w :=
    M.boxCost_image_smul T hunimod eW hE hne (by linarith) w
  have hβt : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent t w) β.val := by
    refine ⟨hβ.1, ?_⟩
    intro γ hγ
    simp only [columnBasisWeight, t, bracketWordExponent_const_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hβ.2 γ hγ) (by linarith)
  obtain ⟨ε, _, hε, hRε⟩ := exists_sequence_subexponential_rate scale R
    (fun n => zero_lt_one.trans_le (hscale1 n)) hR
  obtain ⟨n₀, S, hS, hm⟩ := exists_compact_allowed_cartan_profiles T M F
    hExp realize haarN dynkinN haarD dynkinD X hDnil hletters bD₀ βD hβD b₀ s t
    hweights (fun i => mul_pos (by linarith) (hweights i)) β β hβ hβt
    scale hscale hscale1 ε hε J hJ x
  let r := fun n => scale (n + n₀)
  let A := fun n => M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (r n) 1
  let B := fun n => M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E' β (r n) (R (n + n₀))
  let cells := fun n => (fun p : F.N.carrier × F.N.carrier => p.1 * p.2) '' (A n ×ˢ B n)
  let br := fun n => exponentialRescaleBasis
    (WordBasisSelections.basis X (boundedBracketWords d) βD)
    (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (max (Real.log (r n)) 0)
  let chart := fun n z => F.inclusionD (F.ExpD (F.D.equiv ((br n).equivFun.symm z)))
  have hchart n : Continuous (chart n) := F.closedD.continuous.comp
    (continuous_model_exp_coordinates haarD F.ExpD F.isExpD F.D.equiv
      (F.D.tangent_nilpotent inferInstance) (br n))
  have hmem n q (hq : q ∈ cells n) :
      rescaledContinuousProfile (J (n + n₀)) (hJ (n + n₀)).continuous (x (n + n₀))
        (F.inclusionN q) (max (Real.log (r n)) 0) (chart n) (hchart n) ∈ S := by
    obtain ⟨⟨u, k⟩, ⟨hu, hk⟩, rfl⟩ := hq
    obtain ⟨z, rfl, hz⟩ := hu
    obtain ⟨v, rfl, hv⟩ := hk
    have hv' : ‖(exponentialRescaleBasis
        (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => bracketWordExponent t (β.val i)) (r n)).equivFun v‖ ≤
        Real.exp (r n * ε (n + n₀)) := by
      have hh := hv.trans (hRε (n + n₀))
      change ‖(M.boxBasis T hunimod eW E' β (r n)).equivFun v‖ ≤ _ at hh
      simp only [boxBasis, hcost] at hh
      simpa only [t, s, boxCost, bracketWordExponent_const_mul, r] using hh
    obtain ⟨f, hfs, he⟩ := hm n ((M.boxBasis T hunimod eW E β (r n)).equivFun z) v hz hv'
    have heq : rescaledContinuousProfile (J (n + n₀)) (hJ (n + n₀)).continuous
        (x (n + n₀)) (F.inclusionN ((F.ExpN ∘ F.N.equiv) z * (F.ExpN ∘ F.N.equiv) v))
        (max (Real.log (r n)) 0) (chart n) (hchart n) = f := by
      ext w
      simpa only [boxBasis, s, boxCost, LinearEquiv.symm_apply_apply, map_mul,
        Function.comp_apply, r, chart, br, rescaledContinuousProfile, ContinuousMap.coe_mk]
        using (he w).symm
    exact heq ▸ hfs
  have hcompact (E₀ : Set W) (n : ℕ) (R₀ : ℝ) (hR₀ : 0 ≤ R₀) :
      IsCompact (M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E₀ β (r n) R₀) :=
    isCompact_exponentialCoordinateBox F.N.equiv.toLinearEquiv F.ExpN chartN hchartN
      (M.boxBasis T hunimod eW E₀ β (r n)) R₀ hR₀
  have hmeas n : MeasurableSet (cells n) :=
    (((hcompact E n 1 zero_le_one).prod (hcompact E' n _ (hR0 _))).image
      (continuous_fst.mul continuous_snd)).measurableSet
  have hne' n : (cells n).Nonempty := by
    refine ⟨1, ⟨(1, 1), ⟨?_, ?_⟩, one_mul 1⟩⟩
    · exact ⟨0, by simp [F.isExpN.map_zero], by simp⟩
    · exact ⟨0, by simp [F.isExpN.map_zero], by simpa using hR0 (n + n₀)⟩
  have hprofiles n := exists_measurable_borel_sampled_profile (J (n + n₀))
    (hJ (n + n₀)).continuous (x (n + n₀)) (max (Real.log (r n)) 0) (chart n) (hchart n)
    F.inclusionN F.closedN.continuous.measurable (cells n) (hmeas n) (hne' n) S (hmem n)
  choose profile hp ha using hprofiles
  refine ⟨n₀, S, hS, profile, hp, ?_⟩
  intro n k hk q hq z
  obtain ⟨u, hu, rfl⟩ := hq
  exact ha n (u * k) ⟨(u, k), ⟨hu, hk⟩, rfl⟩ z

end PolycyclicRecognition.CartanWordModel

end

end OAI
