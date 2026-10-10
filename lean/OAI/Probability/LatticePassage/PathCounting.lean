import OAI.Probability.LatticePassage.Lattice
import OAI.Probability.LatticePassage.CheapPath

namespace OAI

namespace CompanionFPP
open Finset

private def neighbors (x : Vertex) : Finset Vertex :=
  {(x.1 + 1, x.2), (x.1 - 1, x.2), (x.1, x.2 + 1), (x.1, x.2 - 1)}

private theorem mem_neighbors {x y : Vertex} : y ∈ neighbors x ↔ lattice.Adj x y := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  change (c,d) ∈ neighbors (a,b) ↔ |a-c| + |b-d| = 1
  simp only [neighbors, mem_insert, mem_singleton, Prod.mk.injEq]
  rcases le_total 0 (a-c) with ha | ha <;>
    rcases le_total 0 (b-d) with hb | hb
  all_goals simp only [abs_of_nonneg, abs_of_nonpos, ha, hb]
  all_goals omega

private theorem card_neighbors (x : Vertex) : (neighbors x).card = 4 := by
  have h₁ : (x.1 + 1, x.2) ≠ (x.1 - 1, x.2) := by intro h; have := congrArg Prod.fst h; omega
  have h₂ : (x.1 + 1, x.2) ≠ (x.1, x.2 + 1) := by intro h; have := congrArg Prod.fst h; omega
  have h₃ : (x.1 + 1, x.2) ≠ (x.1, x.2 - 1) := by intro h; have := congrArg Prod.fst h; omega
  have h₄ : (x.1 - 1, x.2) ≠ (x.1, x.2 + 1) := by intro h; have := congrArg Prod.fst h; omega
  have h₅ : (x.1 - 1, x.2) ≠ (x.1, x.2 - 1) := by intro h; have := congrArg Prod.fst h; omega
  have h₆ : (x.1, x.2 + 1) ≠ (x.1, x.2 - 1) := by intro h; have := congrArg Prod.snd h; omega
  simp [neighbors, h₁,h₂,h₃,h₄,h₅,h₆]

private theorem card_neighbors_erase {prev x : Vertex} (h : lattice.Adj x prev) :
    ((neighbors x).erase prev).card = 3 := by
  rw [card_erase_of_mem (mem_neighbors.mpr h), card_neighbors]

noncomputable def avoidingWalks (n : ℕ) (prev x : Vertex) :
    Finset (Σ y : Vertex, lattice.Walk x y) := by
  classical
  exact match n with
  | 0 => {⟨x, .nil⟩}
  | n+1 => ((neighbors x).erase prev).attach.biUnion fun v =>
      (avoidingWalks n x v).image fun q =>
        ⟨q.1, .cons (mem_neighbors.mp (mem_of_mem_erase v.property)) q.2⟩

theorem card_avoidingWalks (n : ℕ) {prev x : Vertex} (h : lattice.Adj x prev) :
    (avoidingWalks n prev x).card ≤ 3^n := by
  classical
  induction n generalizing prev x with
  | zero => simp [avoidingWalks]
  | succ n ih =>
    calc
      _ ≤ ∑ v ∈ ((neighbors x).erase prev).attach,
          ((avoidingWalks n x v).image (fun q =>
            (⟨q.1, .cons (mem_neighbors.mp (mem_of_mem_erase v.property)) q.2⟩ :
              Σ y : Vertex, lattice.Walk x y))).card := card_biUnion_le
      _ ≤ ∑ _v ∈ ((neighbors x).erase prev).attach, 3^n := by
        apply sum_le_sum
        intro v hv
        exact card_image_le.trans (ih (mem_neighbors.mp (mem_of_mem_erase v.property)).symm)
      _ = 3^(n+1) := by
        simp [card_neighbors_erase h, pow_succ, Nat.mul_comm]

theorem trail_mem_avoiding {prev x y : Vertex} (p : lattice.Walk x y)
    (hp : p.IsTrail) (hne : s(prev,x) ∉ p.edges) :
    (⟨y,p⟩ : Σ y : Vertex, lattice.Walk x y) ∈ avoidingWalks p.length prev x := by
  classical
  induction p generalizing prev with
  | nil => simp [avoidingWalks]
  | @cons x v y h p ih =>
    have ht : p.IsTrail := hp.of_cons
    have hnot : s(x,v) ∉ p.edges := (List.nodup_cons.mp hp.edges_nodup).1
    have hvne : v ≠ prev := by
      intro heq
      subst v
      apply hne
      simp [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
    have hv : v ∈ (neighbors x).erase prev := mem_erase.mpr ⟨hvne, mem_neighbors.mpr h⟩
    simp only [SimpleGraph.Walk.length_cons, avoidingWalks, mem_biUnion]
    refine ⟨⟨v,hv⟩, mem_attach _ _, ?_⟩
    exact mem_image.mpr ⟨⟨y,p⟩, ih ht hnot, rfl⟩

noncomputable def startingWalks (n : ℕ) (x : Vertex) :
    Finset (Σ y : Vertex, lattice.Walk x y) := by
  classical
  exact match n with
  | 0 => {⟨x, .nil⟩}
  | n+1 => (neighbors x).attach.biUnion fun v =>
      (avoidingWalks n x v).image fun q =>
        ⟨q.1, .cons (mem_neighbors.mp v.property) q.2⟩

theorem card_startingWalks (n : ℕ) (x : Vertex) :
    (startingWalks (n+1) x).card ≤ 4 * 3^n := by
  classical
  calc
    _ ≤ ∑ v ∈ (neighbors x).attach,
        ((avoidingWalks n x v).image (fun q =>
          (⟨q.1, .cons (mem_neighbors.mp v.property) q.2⟩ :
            Σ y : Vertex, lattice.Walk x y))).card := card_biUnion_le
    _ ≤ ∑ _v ∈ (neighbors x).attach, 3^n := by
      apply sum_le_sum
      intro v hv
      exact card_image_le.trans (card_avoidingWalks n (mem_neighbors.mp v.property).symm)
    _ = 4 * 3^n := by simp [card_neighbors]

theorem trail_mem_starting {x y : Vertex} (p : lattice.Walk x y) (hp : p.IsTrail) :
    (⟨y,p⟩ : Σ y : Vertex, lattice.Walk x y) ∈ startingWalks p.length x := by
  classical
  cases p with
  | nil => simp [startingWalks]
  | @cons x v y h p =>
    have hnot : s(x,v) ∉ p.edges := (List.nodup_cons.mp hp.edges_nodup).1
    simp only [SimpleGraph.Walk.length_cons, startingWalks, mem_biUnion]
    refine ⟨⟨v,mem_neighbors.mpr h⟩, mem_attach _ _, ?_⟩
    exact mem_image.mpr ⟨⟨y,p⟩, trail_mem_avoiding p hp.of_cons hnot, rfl⟩

end CompanionFPP

end OAI
