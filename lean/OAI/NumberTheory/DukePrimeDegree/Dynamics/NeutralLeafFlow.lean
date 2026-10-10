import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralLeafVersion

namespace OAI

/-!
# Strict neutral invariance at arbitrary real times
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma diagonalOneParameter_rescale_weights
    {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (t : ℝ) :
    diagonalOneParameter (fun r => ell r * t)
      (by rw [← Finset.sum_mul, hell, zero_mul]) 1 = diagonalOneParameter ell hell t := by
  apply Subtype.ext
  simp [diagonalOneParameter]

theorem exists_strictly_neutral_flow_invariant_leafData
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ a : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow a)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∃ V : X (d + 1) → (ℕ × ℕ → ℝ),
      V =ᵐ[μ] intrinsicLeafData hij μ hfree ∧ AEMeasurable V μ ∧
      ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ a, ell a = 0), ell i = ell j →
        ∀ t x, V (rightAction x (diagonalOneParameter ell hell t)) = V x := by
  obtain ⟨V, heq, hm, hv⟩ := exists_strictly_neutral_invariant_leafData d hij μ hA hfree
  refine ⟨V, heq, hm, ?_⟩
  intro ell hell hn t x
  have hsum : ∑ r, ell r * t = 0 := by rw [← Finset.sum_mul, hell, zero_mul]
  have he := hv (fun r => ell r * t) hsum (congrArg (· * t) hn) x
  rwa [diagonalOneParameter_rescale_weights] at he

end DukePrimeDegree

end

end OAI
