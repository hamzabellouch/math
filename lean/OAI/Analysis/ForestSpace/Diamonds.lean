import OAI.Analysis.ForestSpace.Lens

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

namespace ForestSpace

attribute [local instance] Classical.propDecidable

namespace Diamond

/-- An oriented edge enumeration; only the associated undirected unit-edge
simple graph is used for distances. -/
structure Network where
  V : Type
  E : Type
  left : E → V
  right : E → V
  distinct : ∀ e, left e ≠ right e

namespace Network
variable (A : Network)

def graph : SimpleGraph A.V where
  Adj u v := ∃ e : A.E, (A.left e = u ∧ A.right e = v) ∨
    (A.right e = u ∧ A.left e = v)
  symm := ⟨by
    rintro u v ⟨e,h | h⟩
    · exact ⟨e,Or.inr ⟨h.2,h.1⟩⟩
    · exact ⟨e,Or.inl ⟨h.2,h.1⟩⟩⟩
  loopless := ⟨by
    rintro u ⟨e,h | h⟩
    · exact A.distinct e (h.1.trans h.2.symm)
    · exact A.distinct e (h.2.trans h.1.symm)⟩

 theorem edge_adj (e : A.E) : A.graph.Adj (A.left e) (A.right e) :=
  ⟨e,Or.inl ⟨rfl,rfl⟩⟩

/-- Every edge is replaced by countably many internally disjoint two-edge
paths. All old vertices remain, and each pair (edge,index) is a new midpoint. -/
@[reducible] def refine : Network where
  V := Sum A.V (A.E × ℕ)
  E := A.E × ℕ × Bool
  left e := if e.2.2 then Sum.inr (e.1,e.2.1) else Sum.inl (A.left e.1)
  right e := if e.2.2 then Sum.inl (A.right e.1) else Sum.inr (e.1,e.2.1)
  distinct := by rintro ⟨e,j,b⟩; cases b <;> simp

 theorem refine_adj_left (e : A.E) (j : ℕ) :
    A.refine.graph.Adj (Sum.inl (A.left e)) (Sum.inr (e,j)) := by
  exact A.refine.edge_adj (e,j,false)

 theorem refine_adj_right (e : A.E) (j : ℕ) :
    A.refine.graph.Adj (Sum.inr (e,j)) (Sum.inl (A.right e)) := by
  exact A.refine.edge_adj (e,j,true)

 theorem refine_no_adj_middle (a b : A.E × ℕ) :
    ¬A.refine.graph.Adj (Sum.inr a) (Sum.inr b) := by
  rintro ⟨⟨e,j,c⟩,h⟩
  cases c <;> simp [refine] at h

 theorem refine_no_adj_old (u v : A.V) :
    ¬A.refine.graph.Adj (Sum.inl u) (Sum.inl v) := by
  rintro ⟨⟨e,j,c⟩,h⟩
  cases c <;> simp [refine] at h

 theorem refine_adj_lift {u v : A.V} (huv : A.graph.Adj u v) :
    ∃ w : A.refine.V, A.refine.graph.Adj (Sum.inl u) w ∧
      A.refine.graph.Adj w (Sum.inl v) := by
  obtain ⟨e,h | h⟩ := huv
  · rcases h with ⟨rfl,rfl⟩
    exact ⟨Sum.inr (e,0),A.refine_adj_left e 0,A.refine_adj_right e 0⟩
  · rcases h with ⟨rfl,rfl⟩
    exact ⟨Sum.inr (e,0),(A.refine_adj_right e 0).symm,(A.refine_adj_left e 0).symm⟩

 theorem refine_walk_lift {u v : A.V} (p : A.graph.Walk u v) :
    ∃ q : A.refine.graph.Walk (Sum.inl u) (Sum.inl v), q.length = 2*p.length := by
  induction p with
  | nil => exact ⟨.nil,rfl⟩
  | @cons u v w huv p ih =>
    obtain ⟨q,hq⟩ := ih
    obtain ⟨z,huz,hzv⟩ := A.refine_adj_lift huv
    refine ⟨.cons huz (.cons hzv q),?_⟩
    change q.length+1+1 = 2*(p.length+1)
    rw [hq]
    omega

 theorem refine_connected (hA : A.graph.Connected) : A.refine.graph.Connected := by
  have hOld : ∀ u v : A.V, A.refine.graph.Reachable (Sum.inl u) (Sum.inl v) := by
    intro u v
    obtain ⟨p⟩ := hA u v
    obtain ⟨q,hq⟩ := A.refine_walk_lift p
    exact ⟨q⟩
  refine @SimpleGraph.Connected.mk _ _ ?_ ?_
  · intro u v
    cases u with
    | inl u =>
      cases v with
      | inl v => exact hOld u v
      | inr v => exact (hOld u (A.left v.1)).trans (A.refine_adj_left v.1 v.2).reachable
    | inr u =>
      cases v with
      | inl v => exact (A.refine_adj_left u.1 u.2).symm.reachable.trans (hOld (A.left u.1) v)
      | inr v => exact ((A.refine_adj_left u.1 u.2).symm.reachable.trans
          (hOld (A.left u.1) (A.left v.1))).trans (A.refine_adj_left v.1 v.2).reachable
  · obtain ⟨u⟩ := hA.nonempty
    exact ⟨Sum.inl u⟩

end Network

 theorem potential_bound {V : Type} (G : SimpleGraph V) (f : V → ℝ)
    (hf : ∀ u v, G.Adj u v → |f u-f v| ≤ 1) {u v : V} (p : G.Walk u v) :
    |f u-f v| ≤ (p.length : ℝ) := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    have hh := abs_add_le (f u-f v) (f v-f w)
    have he : f u-f v+(f v-f w) = f u-f w := by ring
    rw [he] at hh
    simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
    linarith [hf u v huv]

namespace Network

section
variable (A : Network)

 theorem adj_dist_potential (hA : A.graph.Connected) (a : A.V) {u v : A.V}
    (huv : A.graph.Adj u v) :
    |(A.graph.dist a u : ℝ)-(A.graph.dist a v : ℝ)| ≤ 1 := by
  have he : A.graph.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr huv
  have h1 := hA.dist_triangle (u := a) (v := u) (w := v)
  have h2 := hA.dist_triangle (u := a) (v := v) (w := u)
  rw [he] at h1
  rw [SimpleGraph.dist_comm (u := v) (v := u),he] at h2
  have h1' : (A.graph.dist a v : ℝ) ≤ (A.graph.dist a u : ℝ)+1 := by exact_mod_cast h1
  have h2' : (A.graph.dist a u : ℝ) ≤ (A.graph.dist a v : ℝ)+1 := by exact_mod_cast h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

noncomputable def refinePotential (a : A.V) : A.refine.V → ℝ
  | Sum.inl u => 2*(A.graph.dist a u : ℝ)
  | Sum.inr ⟨e,_⟩ => (A.graph.dist a (A.left e) : ℝ)+(A.graph.dist a (A.right e) : ℝ)

 theorem refinePotential_adj (hA : A.graph.Connected) (a : A.V)
    (u v : A.refine.V) (huv : A.refine.graph.Adj u v) :
    |A.refinePotential a u-A.refinePotential a v| ≤ 1 := by
  obtain ⟨⟨e,j,b⟩,h | h⟩ := huv
  all_goals rcases h with ⟨rfl,rfl⟩
  all_goals cases b
  all_goals dsimp [refine,refinePotential]
  all_goals have hh := A.adj_dist_potential hA a (A.edge_adj e)
  all_goals obtain ⟨h1,h2⟩ := abs_le.mp hh
  all_goals exact abs_le.mpr ⟨by linarith,by linarith⟩

 theorem refine_dist_old (hA : A.graph.Connected) (u v : A.V) :
    A.refine.graph.dist (Sum.inl u) (Sum.inl v) = 2*A.graph.dist u v := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := (hA u v).exists_walk_length_eq_dist
    obtain ⟨q,hq⟩ := A.refine_walk_lift p
    have hh := SimpleGraph.dist_le q
    rwa [hq,hp] at hh
  · obtain ⟨p,hp⟩ := (A.refine_connected hA (Sum.inl u) (Sum.inl v)).exists_walk_length_eq_dist
    have hh := potential_bound A.refine.graph (A.refinePotential u) (A.refinePotential_adj hA u) p
    simp only [refinePotential,SimpleGraph.dist_self,Nat.cast_zero,mul_zero,zero_sub,abs_neg,
      abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),
      abs_of_nonneg (show (0:ℝ) ≤ (A.graph.dist u v : ℝ) from Nat.cast_nonneg _),hp] at hh
    exact_mod_cast hh

 theorem refine_dist_middle (e : A.E) (i j : ℕ) (hij : i ≠ j) :
    A.refine.graph.dist (Sum.inr (e,i)) (Sum.inr (e,j)) = 2 := by
  have he : A.refine.graph.edist (Sum.inr (e,i)) (Sum.inr (e,j)) = 2 := by
    apply SimpleGraph.edist_eq_two_iff.mpr
    refine ⟨?_,A.refine_no_adj_middle _ _,?_⟩
    · intro he
      exact hij (congrArg Prod.snd (Sum.inr.inj he))
    · exact ⟨Sum.inl (A.left e),(A.refine_adj_left e i).symm,(A.refine_adj_left e j).symm⟩
  exact_mod_cast (congrArg ENat.toNat he)

end

/-- Iterating the very same edge replacement, starting from an arbitrary
network. This recursion groups the first replacement before the remaining ones. -/
@[reducible] def iterate : Network → ℕ → Network
  | A,0 => A
  | A,n+1 => iterate A.refine n

/-- The canonical inclusion of all old vertices through finitely many refinements. -/
def old : (A : Network) → (n : ℕ) → A.V → (A.iterate n).V
  | _,0 => id
  | A,n+1 => fun u => A.refine.old n (Sum.inl u)

@[simp] theorem old_zero (A : Network) (u : A.V) : A.old 0 u = u := rfl
@[simp] theorem old_succ (A : Network) (n : ℕ) (u : A.V) :
    A.old (n+1) u = A.refine.old n (Sum.inl u) := rfl

 theorem old_injective (A : Network) (n : ℕ) : Function.Injective (A.old n) := by
  induction n generalizing A with
  | zero => exact Function.injective_id
  | succ n ih => exact (ih A.refine).comp Sum.inl_injective

 theorem iterate_connected (A : Network) (hA : A.graph.Connected) (n : ℕ) :
    (A.iterate n).graph.Connected := by
  induction n generalizing A with
  | zero => exact hA
  | succ n ih => exact ih A.refine (A.refine_connected hA)

 theorem old_dist (A : Network) (hA : A.graph.Connected) (n : ℕ) (u v : A.V) :
    (A.iterate n).graph.dist (A.old n u) (A.old n v) = 2^n*A.graph.dist u v := by
  induction n generalizing A with
  | zero => simp [iterate]
  | succ n ih =>
    change (A.refine.iterate n).graph.dist (A.refine.old n (Sum.inl u))
      (A.refine.old n (Sum.inl v)) = _
    rw [ih A.refine (A.refine_connected hA),A.refine_dist_old hA,pow_succ]
    ring

 theorem old_edge_dist (A : Network) (hA : A.graph.Connected) (n : ℕ) (e : A.E) :
    (A.iterate n).graph.dist (A.old n (A.left e)) (A.old n (A.right e)) = 2^n := by
  rw [A.old_dist hA,SimpleGraph.dist_eq_one_iff_adj.mpr (A.edge_adj e),mul_one]

 theorem old_middle_dist (A : Network) (hA : A.graph.Connected) (n : ℕ) (e : A.E)
    (i j : ℕ) (hij : i ≠ j) :
    (A.iterate (n+1)).graph.dist (A.refine.old n (Sum.inr (e,i)))
      (A.refine.old n (Sum.inr (e,j))) = 2^(n+1) := by
  change (A.refine.iterate n).graph.dist _ _ = _
  rw [A.refine.old_dist (A.refine_connected hA),A.refine_dist_middle e i j hij,pow_succ]

end Network

/-- D₀ is precisely one edge. -/
@[reducible] def base : Network where
  V := Bool
  E := Unit
  left _ := false
  right _ := true
  distinct _ := by decide

 theorem base_connected : base.graph.Connected := by
  refine @SimpleGraph.Connected.mk _ _ ?_ ⟨false⟩
  intro u v
  cases u <;> cases v
  · exact SimpleGraph.Reachable.refl _
  · exact (base.edge_adj ()).reachable
  · exact (base.edge_adj ()).symm.reachable
  · exact SimpleGraph.Reachable.refl _

/-- Countably branching diamonds, all current edges of length one. -/
@[reducible] def diamond (k : ℕ) := base.iterate k

/-- The shortest-path distance, via Mathlib's actual graph distance. -/
def distance (k : ℕ) (u v : (diamond k).V) : ℝ := ((diamond k).graph.dist u v : ℝ)

 theorem diamond_connected (k : ℕ) : (diamond k).graph.Connected :=
  base.iterate_connected base_connected k

/-- Our tail-recursive presentation is exactly successive edge replacement. -/
theorem Network.iterate_succ_refine (A : Network) (n : ℕ) :
    A.iterate (n+1) = (A.iterate n).refine := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih => exact ih A.refine

@[simp] theorem diamond_zero : diamond 0 = base := rfl

theorem diamond_succ (k : ℕ) : diamond (k+1) = (diamond k).refine :=
  Network.iterate_succ_refine base k

theorem Network.iterate_countable (A : Network) [Countable A.V] [Countable A.E]
    (n : ℕ) : Countable (A.iterate n).V ∧ Countable (A.iterate n).E := by
  induction n generalizing A with
  | zero => exact ⟨inferInstance,inferInstance⟩
  | succ n ih => exact ih A.refine

/-- Vertices and edges really are countable at each finite diamond stage. -/
theorem diamond_countable (k : ℕ) : Countable (diamond k).V ∧ Countable (diamond k).E :=
  Network.iterate_countable base k

theorem distance_nonneg (k : ℕ) (u v : (diamond k).V) : 0 ≤ distance k u v := by
  unfold distance
  positivity

theorem distance_eq_zero_iff (k : ℕ) (u v : (diamond k).V) :
    distance k u v = 0 ↔ u = v := by
  rw [distance,Nat.cast_eq_zero]
  exact (diamond_connected k).dist_eq_zero_iff

theorem distance_comm (k : ℕ) (u v : (diamond k).V) :
    distance k u v = distance k v u := by
  unfold distance
  rw [SimpleGraph.dist_comm]

theorem distance_triangle (k : ℕ) (u v w : (diamond k).V) :
    distance k u w ≤ distance k u v+distance k v w := by
  have h : (diamond k).graph.dist u w ≤ (diamond k).graph.dist u v+(diamond k).graph.dist v w :=
    (diamond_connected k).dist_triangle
  unfold distance
  exact_mod_cast h

/-- Every undirected edge has exactly one entry in the oriented enumeration.
Thus refinement replaces genuine graph edges, not a multiset of edges. -/
def Network.UniqueEdges (A : Network) : Prop :=
  ∀ e f : A.E, (A.left e = A.left f ∧ A.right e = A.right f) ∨
    (A.left e = A.right f ∧ A.right e = A.left f) → e = f

theorem Network.refine_uniqueEdges (A : Network) : A.refine.UniqueEdges := by
  rintro ⟨e,i,b⟩ ⟨f,j,c⟩ h
  have he := A.distinct e
  have hf := A.distinct f
  cases b <;> cases c <;> rcases h with h | h <;>
    simp_all [Network.refine,Prod.mk.injEq]
  all_goals aesop

theorem Network.iterate_uniqueEdges (A : Network) (hA : A.UniqueEdges) (n : ℕ) :
    (A.iterate n).UniqueEdges := by
  induction n generalizing A with
  | zero => exact hA
  | succ n ih => exact ih A.refine A.refine_uniqueEdges

theorem diamond_uniqueEdges (k : ℕ) : (diamond k).UniqueEdges :=
  Network.iterate_uniqueEdges base (fun _ _ _ => Subsingleton.elim _ _) k

end Diamond

end ForestSpace

end

end OAI
