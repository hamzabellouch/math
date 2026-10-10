import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.CycleShortening

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem exteriorEdges_le {V : Type*} (G : SimpleGraph V) (X : Set V) :
    exteriorEdges G X ≤ G := fun _ _ h => h.1

 
def OutsidePath {V : Type*} (G : SimpleGraph V) (X : Set V) (x y : V) (d : ℕ) : Prop :=
  x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ ∃ p : G.Walk x y,
    p.IsPath ∧ p.length = d + 1 ∧ ∀ v ∈ p.support, v ∈ X → v = x ∨ v = y

 

def outsideBall {V : Type*} (G : SimpleGraph V) (X : Set V) (x : V) : ℕ → Set V
  | 0 => G.neighborSet x \ X
  | r + 1 => closedNeighborhood G (outsideBall G X x r) \ X

theorem outsideBall_subset_compl {V : Type*} (G : SimpleGraph V) (X : Set V)
    (x : V) (r : ℕ) : outsideBall G X x r ⊆ Xᶜ := by
  cases r <;> exact fun _ h => h.2

theorem outsideBall_subset_succ {V : Type*} (G : SimpleGraph V) (X : Set V)
    (x : V) (r : ℕ) : outsideBall G X x r ⊆ outsideBall G X x (r + 1) :=
  fun _ h => ⟨Or.inl h, outsideBall_subset_compl G X x r h⟩

theorem outsideBall_mono {V : Type*} (G : SimpleGraph V) (X : Set V)
    (x : V) : Monotone (outsideBall G X x) :=
  monotone_nat_of_le_succ (outsideBall_subset_succ G X x)

theorem closedNeighborhood_ball_subset {V : Type*} (G : SimpleGraph V) (X : Set V)
    (x : V) (r : ℕ) :
    closedNeighborhood G (outsideBall G X x r) ⊆ outsideBall G X x (r + 1) ∪ X := by
  intro v hv
  by_cases hx : v ∈ X
  · exact Or.inr hx
  · exact Or.inl ⟨hv, hx⟩

 

theorem outsideBall_walk {V : Type*} {G : SimpleGraph V} {X : Set V} {x z : V}
    {r : ℕ} (hz : z ∈ outsideBall G X x r) :
    ∃ p : (exteriorEdges G X).Walk x z, p.length ≤ r + 1 ∧
      ∀ v ∈ p.support, v = x ∨ v ∉ X := by
  induction r generalizing z with
  | zero =>
    change G.Adj x z ∧ z ∉ X at hz
    let p : (exteriorEdges G X).Walk x z := .cons ⟨hz.1, Or.inr hz.2⟩ .nil
    refine ⟨p, by change 1 ≤ 1; omega, ?_⟩
    dsimp [p]
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hz.2
  | succ r ih =>
    change (z ∈ outsideBall G X x r ∨ ∃ u ∈ outsideBall G X x r, G.Adj u z) ∧ z ∉ X at hz
    rcases hz.1 with hold | ⟨u, hu, huz⟩
    · obtain ⟨p, hp, hs⟩ := ih hold
      exact ⟨p, by omega, hs⟩
    · obtain ⟨p, hp, hs⟩ := ih hu
      refine ⟨p.concat ⟨huz, Or.inr hz.2⟩, ?_, ?_⟩
      · rw [SimpleGraph.Walk.length_concat]
        omega
      · intro v hv
        simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact hs v hv
        · exact Or.inr hz.2

 

theorem outsidePath_of_exterior_walk {V : Type*} {G : SimpleGraph V} {X : Set V}
    {x y : V} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (p : (exteriorEdges G X).Walk x y)
    (hs : ∀ v ∈ p.support, v ∈ X → v = x ∨ v = y) :
    ∃ d, 1 ≤ d ∧ d + 1 ≤ p.length ∧ OutsidePath G X x y d := by
  classical
  let q := p.bypass
  have hq : q.IsPath := p.bypass_isPath
  have hpos : 0 < q.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp
    (fun hn => hxy hn.eq)
  have htwo : 2 ≤ q.length := by
    by_contra hn
    have hh := q.adj_of_length_eq_one (by omega)
    exact hh.2.elim (fun hn => hn hx) (fun hn => hn hy)
  refine ⟨q.length - 1, by omega, ?_, hx, hy, hxy,
    q.mapLe (exteriorEdges_le G X), hq.mapLe _, ?_, ?_⟩
  · have hh := p.length_bypass_le_length; dsimp [q] at *; omega
  · simp only [SimpleGraph.Walk.length_mapLe]; omega
  · intro v hv hvX
    have hvq : v ∈ q.support := by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hv
    exact hs v (p.support_bypass_subset_support hvq) hvX

 
theorem outsidePath_of_balls_meet {V : Type*} {G : SimpleGraph V} {X : Set V}
    {x y z : V} {r s : ℕ} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hzx : z ∈ outsideBall G X x r) (hzy : z ∈ outsideBall G X y s) :
    ∃ d, 1 ≤ d ∧ d ≤ r + s + 1 ∧ OutsidePath G X x y d := by
  obtain ⟨p, hp, hps⟩ := outsideBall_walk hzx
  obtain ⟨q, hq, hqs⟩ := outsideBall_walk hzy
  obtain ⟨d, hd, hlen, hout⟩ := outsidePath_of_exterior_walk hx hy hxy (p.append q.reverse) (by
    intro v hv hvX
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv with hv | hv
    · exact Or.inl ((hps v hv).resolve_right (fun hn => hn hvX))
    · exact Or.inr ((hqs v (by simpa using hv)).resolve_right (fun hn => hn hvX)))
  refine ⟨d, hd, ?_, hout⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at hlen
  omega

 
theorem outsidePath_of_balls_adj {V : Type*} {G : SimpleGraph V} {X : Set V}
    {x y z w : V} {r s : ℕ} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hz : z ∈ outsideBall G X x r) (hw : w ∈ outsideBall G X y s) (hzw : G.Adj z w) :
    ∃ d, 1 ≤ d ∧ d ≤ r + s + 2 ∧ OutsidePath G X x y d := by
  obtain ⟨p, hp, hps⟩ := outsideBall_walk hz
  obtain ⟨q, hq, hqs⟩ := outsideBall_walk hw
  let P := (p.concat ⟨hzw, Or.inl (outsideBall_subset_compl G X x r hz)⟩).append q.reverse
  obtain ⟨d, hd, hlen, hout⟩ := outsidePath_of_exterior_walk hx hy hxy P (by
    intro v hv hvX
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv with hv | hv
    · simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact Or.inl ((hps v hv).resolve_right (fun hn => hn hvX))
      · exact (outsideBall_subset_compl G X y s hw hvX).elim
    · exact Or.inr ((hqs v (by simpa using hv)).resolve_right (fun hn => hn hvX)))
  refine ⟨d, hd, ?_, hout⟩
  dsimp [P] at hlen
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at hlen
  rw [SimpleGraph.Walk.length_concat] at hlen
  omega

theorem outside_balls_separated {V : Type*} {G : SimpleGraph V} {X : Set V}
    {x y : V} {r s : ℕ} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hno : ∀ d, 1 ≤ d → d ≤ r + s + 2 → ¬ OutsidePath G X x y d) :
    Disjoint (outsideBall G X x r) (outsideBall G X y s) ∧
      ∀ z ∈ outsideBall G X x r, ∀ w ∈ outsideBall G X y s, ¬ G.Adj z w := by
  constructor
  · apply Set.disjoint_left.mpr
    intro z hzx hzy
    obtain ⟨d, hd, hd', hp⟩ := outsidePath_of_balls_meet hx hy hxy hzx hzy
    exact hno d hd (by omega) hp
  · intro z hz w hw hzw
    obtain ⟨d, hd, hd', hp⟩ := outsidePath_of_balls_adj hx hy hxy hz hw hzw
    exact hno d hd hd' hp

 
theorem outsidePath_of_ball_adj {V : Type*} {G : SimpleGraph V} {X : Set V}
    {x y z : V} {r : ℕ} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hz : z ∈ outsideBall G X x r) (hzy : G.Adj z y) :
    ∃ d, 1 ≤ d ∧ d ≤ r + 1 ∧ OutsidePath G X x y d := by
  obtain ⟨p, hp, hps⟩ := outsideBall_walk hz
  obtain ⟨d, hd, hlen, hout⟩ := outsidePath_of_exterior_walk hx hy hxy
    (p.concat ⟨hzy, Or.inl (outsideBall_subset_compl G X x r hz)⟩) (by
      intro v hv hvX
      simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact Or.inl ((hps v hv).resolve_right (fun hn => hn hvX))
      · exact Or.inr rfl)
  refine ⟨d, hd, ?_, hout⟩
  rw [SimpleGraph.Walk.length_concat] at hlen
  omega

theorem outside_ball_misses {V : Type*} {G : SimpleGraph V} {X : Set V}
    {x y : V} {r : ℕ} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hno : ∀ d, 1 ≤ d → d ≤ r + 1 → ¬ OutsidePath G X x y d) :
    ∀ z ∈ outsideBall G X x r, ¬ G.Adj z y := by
  intro z hz hzy
  obtain ⟨d, hd, hd', hp⟩ := outsidePath_of_ball_adj hx hy hxy hz hzy
  exact hno d hd hd' hp

attribute [local instance] Classical.propDecidable

end CycleClique

end OAI
