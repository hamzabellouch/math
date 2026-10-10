import OAI.Geometry.DoublingHilbert.Crossings
import OAI.Geometry.DoublingHilbert.Doubling

namespace OAI

/-! A doubling Hilbert subset with no finite-dimensional bi-Lipschitz embedding. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open Metric


section Nonembedding
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A normalized finite-dimensional bi-Lipschitz embedding of the fixed set cannot exist. -/
theorem no_normalized_embedding {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (hlower : ∀ p q, dist p q ≤ dist (f p) (f q)) : False := by
  obtain ⟨bound, hbound⟩ := isCompact_exists_packing_bound
    (isCompact_closedBall (0 : E) (D : ℝ)) (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨z, hz, hsep⟩ := exists_separated_family hf hlower (bound + 1) (by omega)
  have hc := hbound z (fun i => by simpa only [mem_closedBall, dist_zero_right] using hz i) hsep
  omega

/-- Arbitrary positive embedding scales reduce to the normalized obstruction. -/
theorem no_scaled_embedding (f : constructedSet → E) {a D : ℝ}
    (ha : 0 < a) (hD : 1 ≤ D)
    (hf : ∀ x y, a * dist x y ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ D * a * dist x y) : False := by
  let g : constructedSet → E := fun x => a⁻¹ • f x
  let D' : NNReal := ⟨D, le_trans zero_le_one hD⟩
  have hdist (x y : constructedSet) : dist (g x) (g y) = a⁻¹ * dist (f x) (f y) := by
    simp only [g, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha]
  have hg : LipschitzWith D' g := LipschitzWith.of_dist_le_mul fun x y => by
    rw [hdist]
    change a⁻¹ * dist (f x) (f y) ≤ D * dist x y
    calc
      _ ≤ a⁻¹ * (D * a * dist x y) :=
        mul_le_mul_of_nonneg_left (hf x y).2 (inv_nonneg.mpr ha.le)
      _ = _ := by field_simp
  apply no_normalized_embedding hg
  intro x y
  rw [hdist]
  calc
    dist x y = a⁻¹ * (a * dist x y) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hf x y).1 (inv_nonneg.mpr ha.le)

end Nonembedding
end DoublingHilbert

namespace DoublingHilbert

/-- A single fixed subset, independent of dimension and distortion. -/
theorem main : ∃ S : Set RealL2,
    DoublingAtMost S 76800 ∧
      ∀ k : ℕ, 0 < k → ¬ AdmitsBiLipschitzEmbedding S k := by
  refine ⟨constructedSet, ?_, ?_⟩
  · intro x r hr
    exact constructedSet_cover x hr
  · intro k _ hEmbedding
    obtain ⟨f, a, ha, D, hD, hf⟩ := hEmbedding
    exact no_scaled_embedding f ha hD hf

end DoublingHilbert

end OAI
