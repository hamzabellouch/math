import OAI.Probability.DilutedSpin.ConditionalSpatialContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance earliestChildDepthPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {ι : Type} [Fintype ι] {L : ℕ} [NeZero L]

/-- First available proper-child branching depth, with terminal value L
when every proper child is a leaf. This handles the induction endpoint. -/
noncomputable def earliestChildDepth (C : ι → ReducedTopology)
    (q : (j : ι) → (C j).Vertex → Fin L) : ℕ :=
  (Finset.univ.inf (fun w : (j : ι) × (C j).Vertex => (q w.1 w.2).castSucc)).val

omit [NeZero L] in
lemma earliestChildDepth_le_horizon (C : ι → ReducedTopology)
    (q : (j : ι) → (C j).Vertex → Fin L) : earliestChildDepth C q≤L := by
  exact Nat.le_of_lt_succ (Fin.isLt _)

omit [NeZero L] in
lemma earliestChildDepth_le (C : ι → ReducedTopology)
    (q : (j : ι) → (C j).Vertex → Fin L) (j : ι) (v : (C j).Vertex) :
    earliestChildDepth C q≤(q j v).val := by
  have h : Finset.univ.inf (fun w : (j : ι) × (C j).Vertex => (q w.1 w.2).castSucc)≤
      (q j v).castSucc := Finset.inf_le (show (⟨j,v⟩ : (j : ι) × (C j).Vertex) ∈ Finset.univ from Finset.mem_univ _)
  exact h

omit [NeZero L] in
lemma lt_earliestChildDepth (C : ι → ReducedTopology)
    (q : (j : ι) → (C j).Vertex → Fin L) (t : Fin L)
    (ht : ∀ j v, t.val<(q j v).val) : t.val<earliestChildDepth C q := by
  have h : t.succ ≤ Finset.univ.inf (fun w : (j : ι) × (C j).Vertex => (q w.1 w.2).castSucc) := by
    exact Finset.le_inf (fun w _ => show t.val+1≤(q w.1 w.2).val from ht w.1 w.2)
  exact h

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
