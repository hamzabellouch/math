import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionRestriction

namespace OAI

namespace ProjectionComparison

open Set Filter

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

lemma recursion_restrict (S : System V E) (W : Set V) (hW : S.pins⊆W)
    (b h : V → ℝ) (hh : h∈feasible S b) (inc : ℕ → V → ℝ) (N : ℕ)
    (hcut : ∀i<N,∀e,
      recursion S b ⟨h,hh⟩ h inc (i+1) (S.left e)-recursion S b ⟨h,hh⟩ h inc (i+1) (S.right e)=S.cost e →
      S.left e∉S.pins → S.right e∉S.pins → (S.left e∈W ↔ S.right e∈W)) :
    ∀i≤N,(fun x : W => recursion S b ⟨h,hh⟩ h inc i x)=
      recursion (restrictedSystem S W) (fun x => b x)
        ⟨fun x => h x,feasible_restrict S W b h hh⟩ (fun x => h x) (fun i x => inc i x) i := by
  intro i
  induction i with
  | zero => intro hi;rfl
  | succ i ih =>
    intro hi
    have he := ih (Nat.le_of_succ_le hi)
    have hp := projection_restrict S W hW b (fun x => recursion S b ⟨h,hh⟩ h inc i x+inc i x)
      (recursion S b ⟨h,hh⟩ h inc (i+1)) (project_spec S b ⟨h,hh⟩ _) (hcut i (Nat.lt_of_succ_le hi))
    apply projection_unique (restrictedSystem S W) (fun x => b x)
      (fun x => recursion S b ⟨h,hh⟩ h inc i x+inc i x) _ _ hp
    change IsProjection (restrictedSystem S W) (fun x => b x)
      (fun x => (fun x : W => recursion S b ⟨h,hh⟩ h inc i x) x+inc i x) _
    rw [he]
    exact project_spec _ _ _ _

end ProjectionComparison

end OAI
