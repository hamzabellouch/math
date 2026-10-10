import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.BalancedWindows
import OAI.Combinatorics.SharpRamsey.Windows.PreparedWindows

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel ChronologicalTree FreshExecution
open scoped Classical
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k)

lemma representative_window (z : (model w n k p θ G t).FreshHistory) (i : Fin w) (b : Bool) :
    ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,b))).1=i := by
  have hh:=representative_origin_owner w n k p θ G t z (i,b)
  cases b
  · exact (owner_early _ i hh).1
  · exact (owner_late _ i hh).1

lemma representative_before (z : (model w n k p θ G t).FreshHistory)
    (i j : Fin w) (hij : i<j) (b c : Bool) :
    position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,b))) <
      position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (j,c))) :=
  owner_before_next i j hij _ _ (representative_window w n k p θ G t z i b)
    (representative_window w n k p θ G t z j c)

lemma representatives_straddle (z : (model w n k p θ G t).FreshHistory) (i : Fin w) :
    position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,false))) <
      position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,true))) := by
  have he:=owner_early _ i (representative_origin_owner w n k p θ G t z (i,false))
  have hl:=owner_late _ i (representative_origin_owner w n k p θ G t z (i,true))
  unfold position
  rw [he.1,hl.1]
  exact Nat.add_lt_add_left
    (he.2.trans_le ((Nat.le_mul_of_pos_left _ (by decide : 0<3)).trans hl.2)) _

lemma target_before_later (z : (model w n k p θ G t).FreshHistory)
    (i j : Fin w) (hij : i≤j) (x : Fin (2*(n+k))) :
    position ((model w n k p θ G t).origin z.1 (target w n k p θ G t z.1 (i,x))) <
      position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (j,true))) := by
  rcases lt_or_eq_of_le hij with h|rfl
  · rw [target_origin]
    exact owner_before_next i j h _ _ rfl (representative_window w n k p θ G t z j true)
  · exact (target_between w n k p θ G t z i x).2

lemma earlier_before_target (z : (model w n k p θ G t).FreshHistory)
    (i j : Fin w) (hij : i≤j) (x : Fin (2*(n+k))) :
    position ((model w n k p θ G t).origin z.1 ((model w n k p θ G t).representative z (i,false))) <
      position ((model w n k p θ G t).origin z.1 (target w n k p θ G t z.1 (j,x))) := by
  rcases lt_or_eq_of_le hij with h|rfl
  · rw [target_origin]
    exact owner_before_next i j h _ _ (representative_window w n k p θ G t z i false) rfl
  · exact (target_between w n k p θ G t z i x).1

end
end SharpLogRamsey.Selection.Windows

end

end OAI
