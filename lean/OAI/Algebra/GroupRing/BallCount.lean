import Mathlib

namespace OAI



section

/-!
The uniform maximum-degree exclusion bound for finite graph balls.
This treats labelled port graphs too: `neighbors` forgets multiplicities;
loops and multiple edges only decrease the number of distinct vertices.
-/

namespace TorsionFreeZeroDivisors.BallCount

open scoped BigOperators
noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Endpoints of walks of exactly k steps. -/
def ends (neighbors : V → Finset V) (x : V) : ℕ → Finset V
  | 0 => {x}
  | k + 1 => (ends neighbors x k).biUnion neighbors

/-- Finite closed combinatorial ball. -/
def ball (neighbors : V → Finset V) (x : V) (r : ℕ) : Finset V :=
  (Finset.range (r + 1)).biUnion (ends neighbors x)

theorem card_ends_le (neighbors : V → Finset V) (d : ℕ)
    (hd : ∀ v, (neighbors v).card ≤ d) (x : V) (k : ℕ) :
    (ends neighbors x k).card ≤ d ^ k := by
  induction k with
  | zero => simp [ends]
  | succ k ih =>
    calc
      (ends neighbors x (k+1)).card ≤
          ∑ v ∈ ends neighbors x k, (neighbors v).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ ends neighbors x k, d := Finset.sum_le_sum fun v _ => hd v
      _ = (ends neighbors x k).card * d := by simp
      _ ≤ d^k * d := Nat.mul_le_mul_right d ih
      _ = d^(k+1) := (pow_succ d k).symm

/-- A non-asymptotic geometric-sum bound. -/
theorem sum_powers_le (d r : ℕ) (hd : 2 ≤ d) :
    ∑ k ∈ Finset.range (r+1), d^k ≤ 2 * d^r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hp : 0 < d^r := pow_pos (by omega) _
    have hm : 2 * d^r ≤ d^r*d := by nlinarith
    omega

theorem card_ball_le (neighbors : V → Finset V) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, (neighbors v).card ≤ d) (x : V) (r : ℕ) :
    (ball neighbors x r).card ≤ d^(r+1) := by
  calc
    (ball neighbors x r).card ≤ ∑ k ∈ Finset.range (r+1), (ends neighbors x k).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (r+1), d^k :=
      Finset.sum_le_sum fun k _ => card_ends_le neighbors d hd x k
    _ ≤ 2 * d^r - 1 := sum_powers_le d r h2
    _ ≤ d^(r+1) := by
      rw [pow_succ]
      have hm : 2*d^r ≤ d^r*d := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left (d^r) h2
      omega

@[simp] theorem mem_ball_iff (neighbors : V → Finset V) (x y : V) (r : ℕ) :
    y ∈ ball neighbors x r ↔ ∃ k ≤ r, y ∈ ends neighbors x k := by
  simp [ball]

theorem self_mem_ball (neighbors : V → Finset V) (x : V) (r : ℕ) :
    x ∈ ball neighbors x r := by
  rw [mem_ball_iff]
  exact ⟨0,Nat.zero_le _,by simp [ends]⟩

/-- Forgetting parallel edges is sound for the endpoint bound. -/
theorem port_degree_bound {T : Type*} (outgoing : V → Finset T) (next : V → T → V)
    (d : ℕ) (hd : ∀ v, (outgoing v).card ≤ d) (v : V) :
    ((outgoing v).image (next v)).card ≤ d :=
  (Finset.card_image_le).trans (hd v)

/-- The ordinary finite neighbor set, with its classical finiteness data fixed. -/
def graphNeighbors [Fintype V] (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact G.neighborFinset v

omit [DecidableEq V] in
@[simp] theorem mem_graphNeighbors [Fintype V] (G : SimpleGraph V) (a b : V) :
    b ∈ graphNeighbors G a ↔ G.Adj a b := by
  classical
  simp [graphNeighbors]

omit [DecidableEq V] in
theorem card_graphNeighbors [Fintype V] (G : SimpleGraph V) (v : V) :
    (graphNeighbors G v).card = Nat.card (G.neighborSet v) := by
  classical
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
  exact SimpleGraph.card_neighborFinset_eq_degree G v

/-- The finite combinatorial balls contain all walk endpoints, not just paths. -/
theorem mem_ends_of_walk [Fintype V] (G : SimpleGraph V) {a b : V} (p : G.Walk a b) :
    b ∈ ends (graphNeighbors G) a p.length := by
  classical
  induction p using SimpleGraph.Walk.concatRec with
  | Hnil => simp [ends]
  | @Hconcat a b c p h ih =>
    simp only [SimpleGraph.Walk.length_concat,ends,Finset.mem_biUnion]
    exact ⟨b,ih,by simpa using h⟩

theorem mem_ball_of_walk [Fintype V] (G : SimpleGraph V) {a b : V}
    (p : G.Walk a b) (r : ℕ) (hr : p.length ≤ r) : b ∈ ball (graphNeighbors G) a r := by
  exact mem_ball_iff _ _ _ _ |>.mpr ⟨p.length,hr,mem_ends_of_walk G p⟩

theorem far_of_not_mem_ball [Fintype V] (G : SimpleGraph V) {a b : V} (r : ℕ)
    (h : b ∉ ball (graphNeighbors G) a r) (p : G.Walk a b) : r < p.length := by
  by_contra hn
  exact h (mem_ball_of_walk G p r (by omega))

section Matchings
variable {X Y : Type*} [Fintype X] [DecidableEq X]

/-- Removing source and target ports in a bad vertex set discards at most twice
its cardinality, since each labelled carrier embeds in the vertex set. -/
theorem matching_bad_card (f : X ≃ Y) (locX : X → V) (locY : Y → V)
    (hX : Function.Injective locX) (hY : Function.Injective locY) (B : Finset V) :
    (Finset.univ.filter (fun u => locX u ∈ B ∨ locY (f u) ∈ B)).card ≤ 2 * B.card := by
  classical
  have hx : (Finset.univ.filter (fun u => locX u ∈ B)).card ≤ B.card := by
    apply Finset.card_le_card_of_injOn locX
    · intro u hu; exact (Finset.mem_filter.mp hu).2
    · exact hX.injOn
  have hy : (Finset.univ.filter (fun u => locY (f u) ∈ B)).card ≤ B.card := by
    apply Finset.card_le_card_of_injOn (fun u => locY (f u))
    · intro u hu; exact (Finset.mem_filter.mp hu).2
    · exact (hY.comp f.injective).injOn
  rw [Finset.filter_or]
  exact (Finset.card_union_le _ _).trans (by omega)

/-- A labelled matching has uniformly many choices outside both endpoint balls
and outside a prescribed set. This is the quantitative geometric input to the
conditioned transposition injection. -/
theorem admissible_card (f : X ≃ Y) (locX : X → V) (locY : Y → V)
    (hX : Function.Injective locX) (hY : Function.Injective locY)
    (neighbors : V → Finset V) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, (neighbors v).card ≤ d) (x y : V) (r : ℕ) (P : Finset X) :
    Fintype.card X - P.card - 4*d^(r+1) ≤
      (Finset.univ.filter (fun u => u ∉ P ∧
        locX u ∉ ball neighbors x r ∪ ball neighbors y r ∧
        locY (f u) ∉ ball neighbors x r ∪ ball neighbors y r)).card := by
  classical
  let B := ball neighbors x r ∪ ball neighbors y r
  let bad := Finset.univ.filter (fun u => locX u ∈ B ∨ locY (f u) ∈ B)
  have hb : bad.card ≤ 4*d^(r+1) := by
    have hb' := matching_bad_card f locX locY hX hY B
    have hB : B.card ≤ 2*d^(r+1) :=
      (Finset.card_union_le _ _).trans (by
        have hx := card_ball_le neighbors d h2 hd x r
        have hy := card_ball_le neighbors d h2 hd y r
        omega)
    exact hb'.trans (by omega)
  have he : Finset.univ.filter (fun u => u ∉ P ∧ locX u ∉ B ∧ locY (f u) ∉ B) =
      Finset.univ \ (P ∪ bad) := by
    ext u
    simp [bad, not_or]
  change _ ≤ (Finset.univ.filter (fun u => u ∉ P ∧ locX u ∉ B ∧ locY (f u) ∉ B)).card
  rw [he,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
  have hu := Finset.card_union_le P bad
  omega

end Matchings
end
end TorsionFreeZeroDivisors.BallCount


/-!
A faithful simple-graph encoding of the manuscript's labelled multigraphs.
An original edge has two opposite ports, and its threefold subdivision is
original vertex -- port -- opposite port -- original vertex. Loops become
triangles and parallel edges remain distinct, so neither is silently discarded.
-/

end

end OAI
