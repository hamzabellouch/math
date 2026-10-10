import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanInverseSections
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSegmentWordPath

namespace OAI

/-! # Continuous endpoint families in actual segment boxes

A common coordinate ball parametrizes true endpoints in every maximizing
rescaled box. The chosen support paths have continuous time samples and
uniform bounds, so coordinates can be sampled independently of normalized
quasi-isometry pairs.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

include T in
/-- Actual segment-box endpoints have continuously sampled paths on a
common positive-radius coordinate ball, with uniform coarse metric bounds. -/
theorem exists_continuous_segment_box_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (v : H) :
    ∃ (ε C : ℝ), 0 < ε ∧ 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent (M.segmentSupportExponent v) w) β.val →
      let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent (M.segmentSupportExponent v) (β.val j)) r
      ∃ γ : ∀ y : ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε,
          Path (1 : G) (F.inclusionN (F.ExpN (F.N.equiv (b.equivFun.symm y.val)))),
        (∀ t, Continuous (fun y => γ y t)) ∧
        (∀ y, PathMetricBound (γ y) (C * r) (C * (1 + Real.log (2 + r)))) ∧
        ∀ y t, ∃ z ∈ segment ℝ (0 : W) (l (Exp v)).toAdd, (l (γ y t)).toAdd = r • z := by
  classical
  obtain ⟨ε, N, B, hε, hB, hcode⟩ :=
    M.exists_uniform_cartan_inverse_sections T F hExp realize haarN dynkinN b₀
  obtain ⟨C, hC, hpath⟩ := M.exists_segmentWordPath_bound T hExp realize l hl hL hbound
    v (by linarith : 0 ≤ B) N
  refine ⟨ε, C, hε, hC, ?_⟩
  intro r hr β hβ b
  obtain ⟨w, i, σ, hσ, hs⟩ := hcode (M.segmentSupportExponent v) β hβ r hr
  let Y := ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε
  let σ' : Y → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ := fun y => σ y.val
  have hσ' : Continuous σ' := continuousOn_iff_continuous_domRestrict.mp hσ
  let u (y : Y) := generatorSchemeWord w i (σ' y)
  have hspec (y : Y) := hs y.val y.property
  have hword (z : List (Fin M.letterCount × ℝ)) :
      ((M.segmentScaledWord v r z).map
        (fun q => Exp (q.2 • (M.letter q.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).prod =
      F.inclusionN (generatorGroupWord
        (fun j => Real.exp (r * M.segmentSupportExponent v j) • M.letter j)
        (F.ExpN ∘ F.N.equiv) z) := by
    simp only [segmentScaledWord, List.map_map, generatorGroupWord, map_list_prod]
    apply congrArg List.prod
    apply List.map_congr_left
    intro q _
    dsimp only [Function.comp_apply]
    rw [F.compatibleN]
    simp only [SetLike.val_smul, smul_smul]
  have hend (y : Y) :
      F.inclusionN (F.ExpN (F.N.equiv (b.equivFun.symm y.val))) =
      ((M.segmentScaledWord v r (u y)).map
        (fun q => Exp (q.2 • (M.letter q.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).prod := by
    exact ((hword (u y)).trans (congrArg F.inclusionN (hspec y).2.2.2)).symm
  let γ (y : Y) := (M.segmentWordPath T hExp realize v r (u y)).cast rfl (hend y)
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro t
    have hc := M.continuous_segmentWordPath_sample T hExp realize v r
      (parameterGeneratorSchemeWord w i σ')
      (parameterGeneratorSchemeWord_continuous w i σ' hσ') t
    have he : (fun y : Y => M.segmentWordPath T hExp realize v r
        ((parameterGeneratorSchemeWord w i σ').map (fun z => (z.1, z.2 y))) t) =
        (fun y : Y => M.segmentWordPath T hExp realize v r (u y) t) := by
      funext y
      exact congrArg (fun z => M.segmentWordPath T hExp realize v r z t)
        (parameterGeneratorSchemeWord_eval w i σ' y)
    rw [he] at hc
    exact hc
  · intro y
    exact ((hpath r hr (u y) (hspec y).2.1 (hspec y).2.2.1).1).cast rfl (hend y)
  · intro y t
    exact (hpath r hr (u y) (hspec y).2.1 (hspec y).2.2.1).2 t

end PolycyclicRecognition.CartanWordModel

end

end OAI
