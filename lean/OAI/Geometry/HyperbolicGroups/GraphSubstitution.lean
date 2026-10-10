import Mathlib
import OAI.Geometry.HyperbolicGroups.GraphWordFilling

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.GraphWordFilling
open SimpleGraph
variable {V W A : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

lemma word_reverse (r : G.Dart → A × Bool)
    (hr : ∀ e, r e.symm = ((r e).1,!(r e).2)) {u v : V} (p : G.Walk u v) :
    word r p.reverse = FreeGroup.invRev (word r p) := by
  simp only [word,Walk.darts_reverse,List.map_reverse,List.map_map,FreeGroup.invRev]
  congr 1
  apply List.map_congr_left
  intro e he
  exact hr e

/-- Replace each oriented edge by a prescribed genuine edge-path. Endpoints
are enforced in the type, thereby preserving closedness exactly. -/
def expand (f : V → W) (r : ∀ {u v}, G.Adj u v → H.Walk (f u) (f v)) :
    {u v : V} → G.Walk u v → H.Walk (f u) (f v)
  | _,_,.nil => .nil
  | _,_,.cons h p => (r h).append (expand f r p)

lemma expand_length (f : V → W) (r : ∀ {u v}, G.Adj u v → H.Walk (f u) (f v))
    (L : ℕ) (hr : ∀ {u v} (h : G.Adj u v), (r h).length ≤ L)
    {u v : V} (p : G.Walk u v) : (expand f r p).length ≤ L * p.length := by
  induction p with
  | nil => simp [expand]
  | cons h p ih =>
    simp only [expand,Walk.length_append,Walk.length_cons,Nat.mul_add,Nat.mul_one]
    exact (Nat.add_le_add (hr h) ih).trans_eq (Nat.add_comm _ _)

lemma expand_word (f : V → W) (r : ∀ {u v}, G.Adj u v → H.Walk (f u) (f v))
    (l : H.Dart → A × Bool) {u v : V} (p : G.Walk u v) :
    word l (expand f r p) = p.darts.flatMap (fun e => word l (r e.adj)) := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [expand,word_append,ih,Walk.darts_cons,List.flatMap_cons]

end HyperbolicObstruction.GraphWordFilling
end
end

section

end
end

end OAI
