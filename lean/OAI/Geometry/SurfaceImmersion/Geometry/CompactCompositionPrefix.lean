import OAI.Geometry.SurfaceImmersion.Geometry.LowJetPrefixBounds
import OAI.Geometry.SurfaceImmersion.Geometry.CompactLocalBounds
import OAI.Geometry.Immersion.ClosedSurface.CoordinateBounds

namespace OAI

/-! Fixed smooth changes of coordinates preserve the second-order
rescaled derivative profile needed by the primitive recursion. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem compact_composition_prefix {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    {S : Set Base} (hS : IsOpen S) (hSc : IsCompact (closure S)) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (f : Base → Space) (s C : ℝ),
      0 < s → 0 ≤ C → ContDiff ℝ ∞ f →
      (∀ j, j ≤ m+2 → WeightedBound univ 1 j (C/s^(j-2)) f) →
      ∀ j, j ≤ m+2 → WeightedBound S 1 j (D*C/s^(j-2)) (f ∘ T) := by
  obtain ⟨B,hB,hTb⟩ := compact_local_weighted_bound hS isOpen_univ hSc
    subset_closure (subset_univ _) hT.contDiffOn (m+2)
  let D : ℝ := ((m+2).factorial : ℝ)*B^(m+2)
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast Nat.factorial_pos (m+2)) (one_le_pow₀ hB)
  refine ⟨D,hD,?_⟩
  intro f s C hs hC hf hb j hj
  have hcoord : ∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ S,
      ‖iteratedFDerivWithin ℝ k T S x‖ ≤ B := by
    intro k _ hk x hx
    simpa only [one_pow,one_mul] using hTb 1 zero_le_one le_rfl k (hk.trans hj) x hx
  have hh := (hb j hj).comp_coordinates hS.uniqueDiffOn uniqueDiffOn_univ zero_lt_one le_rfl
    hB (div_nonneg hC (pow_nonneg hs.le _)) hT.contDiffOn hf.contDiffOn
    (fun _ _ => mem_univ _) hcoord
  have hc : (j.factorial : ℝ)*B^j ≤ D := mul_le_mul
    (by exact_mod_cast Nat.factorial_le hj)
    (pow_le_pow_right₀ hB hj) (by positivity) (by positivity)
  apply hh.mono_const
  calc
    (j.factorial : ℝ)*(C/s^(j-2))*B^j = ((j.factorial : ℝ)*B^j)*(C/s^(j-2)) := by ring
    _ ≤ D*(C/s^(j-2)) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = D*C/s^(j-2) := by ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI
