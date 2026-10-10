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

theorem compact_composition_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    {S : Set Base} (hS : IsOpen S) (hSc : IsCompact (closure S)) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (f : Base → E) (C : ℝ),
      0 ≤ C → ContDiff ℝ ∞ f → WeightedBound univ 1 m C f →
      WeightedBound S 1 m (D*C) (f ∘ T) := by
  obtain ⟨B,hB,hTb⟩ := compact_local_weighted_bound hS isOpen_univ hSc
    subset_closure (subset_univ _) hT.contDiffOn m
  let D : ℝ := (m.factorial : ℝ)*B^m
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast Nat.factorial_pos m) (one_le_pow₀ hB)
  refine ⟨D,hD,?_⟩
  intro f C hC hf hb
  have hcoord : ∀ k, 1 ≤ k → k ≤ m → ∀ x ∈ S,
      ‖iteratedFDerivWithin ℝ k T S x‖ ≤ B := by
    intro k _ hk x hx
    simpa only [one_pow,one_mul] using hTb 1 zero_le_one le_rfl k hk x hx
  have hh := hb.comp_coordinates hS.uniqueDiffOn uniqueDiffOn_univ zero_lt_one le_rfl
    hB hC hT.contDiffOn hf.contDiffOn (fun _ _ => mem_univ _) hcoord
  convert hh using 1
  dsimp only [D]
  ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI
