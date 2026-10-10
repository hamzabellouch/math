import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTemplateCoding
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedInverseCoding

namespace OAI

/-! # Continuous probe paths on an entire bounded Cartan box

The local inverse scheme is repeated after dividing logarithms by one
fixed integer. Both the number of switches and their amplitudes are
uniform over the scale and maximizing basis. Every path sample remains
continuous in the original box coordinate, which supplies the measurable
choices required in the independent-probe argument.
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
omit [IsIsometricSMul G G] in
theorem exists_continuous_bounded_template_coding
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (v : Fin M.letterCount → H) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent (M.templateSupportExponent v) w) β.val →
      let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent (M.templateSupportExponent v) (β.val j)) r
      ∃ word : List (Fin M.letterCount ×
          (closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R → ℝ)),
        word.length ≤ N ∧ (∀ z ∈ word, Continuous z.2) ∧
        (∀ y, ∀ z ∈ word, |z.2 y| ≤ C) ∧
        ∀ y, generatorGroupWord
          (fun i => Real.exp (r * M.templateSupportExponent v i) • M.letter i)
          (F.ExpN ∘ F.N.equiv) (word.map (fun z => (z.1, z.2 y))) =
            F.ExpN (F.N.equiv (b.equivFun.symm y.val)) := by
  obtain ⟨ε, N, C, hε, hC, hcode⟩ :=
    M.exists_uniform_template_inverse_sections T F hExp realize haarN dynkinN b₀ v
  obtain ⟨k, hk⟩ := exists_nat_gt (max (R / ε) 0)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (le_max_right _ _) hk
  have hkR : R < (k : ℝ) * ε :=
    (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_left _ _) hk)
  refine ⟨k * N, C, hC, ?_⟩
  intro r hr β hβ b
  obtain ⟨w, i, σ, hσ, hs⟩ := hcode β hβ r hr
  apply bounded_continuous_generator_coding
    (fun i => Real.exp (r * M.templateSupportExponent v i) • M.letter i)
    (F.ExpN ∘ F.N.equiv) b.equivFun.symm.toLinearMap
    (by simp [F.isExpN.map_zero])
    (fun x s t => by
      simpa only [Function.comp_apply, map_smul] using
        F.isExpN.map_add_smul (F.N.equiv x) s t)
    w i σ hσ (fun y hy => ⟨(hs y hy).2.1, (hs y hy).2.2⟩) R hR k hk0 hkR

include T in
omit [IsIsometricSMul G G] in
private theorem template_path_family_from_word
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    {Y : Type*} [TopologicalSpace Y]
    (v : Fin M.letterCount → H) (r C : ℝ)
    (l : G →* Multiplicative W) (E : Set W)
    (word : List (Fin M.letterCount × (Y → ℝ)))
    (hc : ∀ z ∈ word, Continuous z.2)
    (target : Y → G)
    (he : ∀ y, target y =
      ((M.templateScaledWord v r (word.map (fun z => (z.1, z.2 y)))).map
        (fun z => Exp (z.2 • (M.letter z.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).prod)
    (hb : ∀ y,
      PathMetricBound (M.templateWordPath T hExp realize v r
        (word.map (fun z => (z.1, z.2 y))))
        (C * r) (C * (1 + Real.log (2 + r))) ∧
      ∀ t, ∃ z ∈ E,
        (l (M.templateWordPath T hExp realize v r
          (word.map (fun z => (z.1, z.2 y))) t)).toAdd = r • z) :
    ∃ γ : ∀ y : Y, Path (1 : G) (target y),
      (∀ t, Continuous (fun y => γ y t)) ∧
      (∀ y, PathMetricBound (γ y) (C * r) (C * (1 + Real.log (2 + r)))) ∧
      ∀ y t, ∃ z ∈ E, (l (γ y t)).toAdd = r • z := by
  let γ : ∀ y : Y, Path (1 : G) (target y) := fun y =>
    (M.templateWordPath T hExp realize v r (word.map (fun z => (z.1, z.2 y)))).cast
      rfl (he y)
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro t
    exact M.continuous_templateWordPath_sample T hExp realize v r word hc t
  · intro y
    exact (hb y).1.cast rfl (he y)
  · intro y t
    exact (hb y).2 t

include T in
/-- Whole-box endpoint selectors with continuous samples, controlled
length, and the prescribed template height range. -/
theorem exists_continuous_bounded_template_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (v : Fin M.letterCount → H)
    (E : Set W) (hE : Convex ℝ E) (hE0 : (0 : W) ∈ E)
    (hvE : ∀ i, (l (Exp (v i))).toAdd ∈ E) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent (M.templateSupportExponent v) w) β.val →
      let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent (M.templateSupportExponent v) (β.val j)) r
      ∃ γ : ∀ y : closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R,
          Path (1 : G) (F.inclusionN (F.ExpN (F.N.equiv (b.equivFun.symm y.val)))),
        (∀ t, Continuous (fun y => γ y t)) ∧
        (∀ y, PathMetricBound (γ y) (C * r) (C * (1 + Real.log (2 + r)))) ∧
        ∀ y t, ∃ z ∈ E, (l (γ y t)).toAdd = r • z := by
  classical
  obtain ⟨N, B, hB, hcode⟩ :=
    M.exists_continuous_bounded_template_coding T F hExp realize haarN dynkinN b₀ v R hR
  obtain ⟨C, hC, hpath⟩ := M.exists_templateWordPath_bound T hExp realize l hl hL hbound
    v E hE hE0 hvE (by linarith : 0 ≤ B) N
  refine ⟨C, hC, ?_⟩
  intro r hr β hβ b
  have code := hcode r hr β hβ
  dsimp only at code
  let word := code.choose
  have hlen := code.choose_spec.1
  have hcont := code.choose_spec.2.1
  have hamp := code.choose_spec.2.2.1
  have hend := code.choose_spec.2.2.2
  let Y := closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R
  let u (y : Y) := word.map (fun z => (z.1, z.2 y))
  have hu (y : Y) : (u y).length ≤ N := by simpa only [u, List.length_map] using hlen
  have hub (y : Y) : ∀ z ∈ u y, |z.2| ≤ B := by
    intro z hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact hamp y z' hz'
  have he (y : Y) : F.inclusionN (F.ExpN (F.N.equiv (b.equivFun.symm y.val))) =
      ((M.templateScaledWord v r (u y)).map
        (fun z => Exp (z.2 • (M.letter z.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).prod :=
    ((M.templateScaledWord_product F v r (u y)).trans (congrArg F.inclusionN (hend y))).symm
  exact M.template_path_family_from_word T hExp realize v r C l E word hcont
    (fun y => F.inclusionN (F.ExpN (F.N.equiv (b.equivFun.symm y.val)))) he
    (fun y => hpath r hr (u y) (hu y) (hub y))

end PolycyclicRecognition.CartanWordModel

end

end OAI
