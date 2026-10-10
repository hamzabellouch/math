import OAI.Analysis.Nonexpansive.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.OrderClosed

namespace OAI

/-!
# One vector satisfying every branch halfspace

The finite-prefix witnesses lie in the same actual weakly compact set.
Continuous linear evaluations define weakly closed halfspaces. Compactness
then keeps one vector in all the constraints. In the final application the
set is the whole unit ball of the closed difference span, viewed in X.
-/

namespace ReflexiveFixedPoints

/-- Finite-prefix feasibility in an actual weakly compact set gives one point
in every halfspace. Only scalar linear evaluations use weak continuity. -/
theorem exists_weaklyCompact_all_halfspaces
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : Set X) (hB : WeaklyCompact B)
    (f : ℕ → X →L[ℝ] ℝ) (c : ℝ)
    (hPrefix : ∀ n : ℕ, ∃ x ∈ B, ∀ i < n, c ≤ f i x) :
    ∃ x ∈ B, ∀ i, c ≤ f i x := by
  classical
  let H : ℕ → Set (WeakSpace ℝ X) :=
    fun i => {w | c ≤ f i ((toWeakSpace ℝ X).symm w)}
  have hclosed (i : ℕ) : IsClosed (H i) :=
    isClosed_le continuous_const
      (WeakBilin.eval_continuous (topDualPairing ℝ X).flip (f i))
  have hfinite (s : Finset ℕ) :
      (((toWeakSpace ℝ X) '' B) ∩ ⋂ i ∈ s, H i).Nonempty := by
    obtain ⟨x, hx, hfx⟩ := hPrefix (s.sup id + 1)
    refine ⟨toWeakSpace ℝ X x, ⟨x, hx, rfl⟩, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    change c ≤ f i ((toWeakSpace ℝ X).symm (toWeakSpace ℝ X x))
    simpa only [LinearEquiv.symm_apply_apply] using
      hfx i (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have hcompact : IsCompact ((toWeakSpace ℝ X) '' B) := hB
  obtain ⟨w, hwB, hwH⟩ := hcompact.inter_iInter_nonempty H hclosed hfinite
  obtain ⟨x, hx, rfl⟩ := hwB
  refine ⟨x, hx, ?_⟩
  intro i
  have hi := Set.mem_iInter.mp hwH i
  simpa only [H, Set.mem_ofPred_eq, LinearEquiv.symm_apply_apply] using hi

end ReflexiveFixedPoints

end OAI
