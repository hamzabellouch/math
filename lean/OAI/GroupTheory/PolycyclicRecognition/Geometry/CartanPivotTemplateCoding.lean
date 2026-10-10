import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundedTemplatePaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTemplateSupports
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPivotWordPath

namespace OAI

/-! # Continuous box selectors independent of the starting sheet

The actual generator word is retained, so its finitely many prefix sheets
can be used in the independent-probe concentration argument.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The selector is chosen before both the starting sheet and the pivot.
It has uniformly bounded length and amplitudes, and every evaluation is
continuous on the entire closed coordinate ball. -/
theorem exists_continuous_pivot_template_coding
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (hE : IsCompact E) (hconv : Convex ℝ E) {w₀ : W} (hw₀ : w₀ ∈ E)
    (R : ℝ) (hR : 0 ≤ R) {A : ℝ} (hA : 0 ≤ A) (p : ℕ) :
    ∃ (v : Fin M.letterCount → H) (N : ℕ) (B C : ℝ),
      1 ≤ B ∧ 0 ≤ C ∧
      (∀ i, eW (heightProjection T.character (v i)) ∈ E) ∧
      M.templateSupportExponent v = (M.supportIn T hunimod eW).weightSupport E ∧
      ∀ r : ℝ, 0 ≤ r → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∃ word : List (Fin M.letterCount ×
          (closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R → ℝ)),
        word.length ≤ N ∧ (∀ z ∈ word, Continuous z.2) ∧
        (∀ y, ∀ z ∈ word, |z.2 y| ≤ B) ∧
        (∀ y, indexedWordProduct (M.rootFlow (Exp := Exp))
          (M.templateScaledWord v r (word.map (fun z => (z.1, z.2 y)))) =
            F.inclusionN (F.ExpN (F.N.equiv
              ((M.boxBasis T hunimod eW E β r).equivFun.symm y.val)))) ∧
        ∀ h₀ : H, ‖(finBasis ℝ H).equivFun h₀‖ ≤ A * (1 + r) ^ p →
          (π (Exp h₀)).toAdd = r • w₀ → ∀ y, ∀ n : G, π n = 1 →
          PathMetricBound
            (M.pivotWordPath T hExp realize eW w₀
              (fun i => eW (heightProjection T.character (v i))) h₀ r
              (M.templateScaledWord v r (word.map (fun z => (z.1, z.2 y)))) n)
            (C * r) (C * (1 + Real.log (2 + r))) ∧
          ∀ t, ∃ z ∈ E,
            (π (M.pivotWordPath T hExp realize eW w₀
              (fun i => eW (heightProjection T.character (v i))) h₀ r
              (M.templateScaledWord v r (word.map (fun z => (z.1, z.2 y)))) n t)).toAdd = r • z := by
  obtain ⟨v, hv, hs⟩ := M.exists_cartan_template_supports T hunimod eW E hE ⟨w₀, hw₀⟩
  obtain ⟨N, B, hB, hcode⟩ := M.exists_continuous_bounded_template_coding T F hExp realize
    haarN dynkinN b₀ v R hR
  let w := fun i => eW (heightProjection T.character (v i))
  have hw i : w i ∈ E := hv i
  have hws i : cartanHeightWeight T H (M.weight i) (eW.symm (w i)) =
      (M.supportIn T hunimod eW).weightSupport E i := by
    rw [← hs]
    simp only [w, eW.symm_apply_apply]
    exact cartanHeightWeight_projection T H (M.weight i) (v i)
  obtain ⟨C, hC, hb⟩ := M.exists_pivotWordPath_bound T hExp realize eW F
    haarD dynkinD π hπ hconv hw₀ w hw
    ((M.supportIn T hunimod eW).weightSupport E) hws hA (by linarith : 0 ≤ B) p N
  refine ⟨v, N, B, C, hB, hC, hv, hs, ?_⟩
  intro r hr β hβ
  change IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
    (fun z => bracketWordExponent ((M.supportIn T hunimod eW).weightSupport E) z) β.val at hβ
  have hβ' : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun z => bracketWordExponent (M.templateSupportExponent v) z) β.val := by
    simpa only [hs] using hβ
  obtain ⟨word, hlen, hcont, hamp, hend⟩ := hcode r hr β hβ'
  refine ⟨word, hlen, hcont, hamp, ?_, ?_⟩
  · intro y
    have he := M.templateScaledWord_product F v r (word.map (fun z => (z.1, z.2 y)))
    change indexedWordProduct (M.rootFlow (Exp := Exp))
      (M.templateScaledWord v r (word.map (fun z => (z.1, z.2 y)))) = _ at he
    rw [he]
    have hh := congrArg F.inclusionN (hend y)
    change F.inclusionN (generatorGroupWord
      (fun i => Real.exp (r * M.templateSupportExponent v i) • M.letter i)
      (F.ExpN ∘ F.N.equiv) (word.map (fun z => (z.1, z.2 y)))) = _
    simpa only [hs, boxBasis, boxCost] using hh
  · intro h₀ hnorm hheight y n hn
    apply hb r hr h₀ hnorm hheight _ (by
      simpa only [templateScaledWord, List.length_map] using hlen) ?_ n hn
    intro z hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
    obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hu
    dsimp only
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    change |u'.2 y| * Real.exp (r * M.templateSupportExponent v u'.1) ≤ _
    rw [hs]
    exact mul_le_mul_of_nonneg_right (hamp y u' hu') (Real.exp_pos _).le

end PolycyclicRecognition.CartanWordModel

end

end OAI
