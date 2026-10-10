import OAI.NumberTheory.DukePrimeDegree.Geometry.EliminationChain

namespace OAI

/-!
# Existence of the complete ordered elimination chain

At each step choose the least remaining positive root in row order.
The processed roots form an initial segment, which proves exactly the
zero-preservation and pivot conditions required by the next chart.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def allPositiveRoots (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

def InitialRootPattern {n : ℕ} (P : Finset (Fin n × Fin n)) : Prop :=
  ∀ p ∈ P, p ∈ allPositiveRoots n ∧
    ∀ q ∈ allPositiveRoots n, toLex q < toLex p → q ∈ P

def PivotsFromPattern {n : ℕ} (P : Finset (Fin n × Fin n)) (D : Finset (Fin n)) : Prop :=
  ∀ a ∈ D, ∃ b, (a, b) ∈ P

lemma initialRootPattern_stable {n : ℕ} {P : Finset (Fin n × Fin n)}
    (hP : InitialRootPattern P) {a b : Fin n} (hab : a < b) (habP : (a, b) ∉ P) :
    ∀ r, (r, b) ∈ P → (r, a) ∈ P := by
  intro r hr
  have hra : r < a := by
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hlt | he
    · exact habP ((hP (r, b) hr).2 (a, b)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)
        (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)))
    · subst r
      exact habP hr
  exact (hP (r, b) hr).2 (r, a)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hra⟩)
    (Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hab⟩))

lemma initialRootPattern_pivot_notMem {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (hP : InitialRootPattern P) (hD : PivotsFromPattern P D)
    {a b : Fin n} (hab : a < b) (habP : (a, b) ∉ P) : b ∉ D := by
  intro hb
  obtain ⟨c, hc⟩ := hD b hb
  exact habP ((hP (b, c) hc).2 (a, b)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)
    (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hab)))

lemma initialRootPattern_insert_min {n : ℕ} {P : Finset (Fin n × Fin n)}
    (hP : InitialRootPattern P) (p : Fin n × Fin n)
    (hp : p ∈ allPositiveRoots n \ P)
    (hmin : ∀ q ∈ allPositiveRoots n \ P, toLex p ≤ toLex q) :
    InitialRootPattern (insert p P) := by
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · refine ⟨(Finset.mem_sdiff.mp hp).1, ?_⟩
    intro q hq hqp
    by_cases hqP : q ∈ P
    · exact Finset.mem_insert_of_mem hqP
    · exact (not_lt_of_ge (hmin q (Finset.mem_sdiff.mpr ⟨hq, hqP⟩)) hqp).elim
  · exact ⟨(hP q hq).1, fun r hr hrq => Finset.mem_insert_of_mem ((hP q hq).2 r hr hrq)⟩

lemma pivotsFromPattern_insert {n : ℕ} {P : Finset (Fin n × Fin n)}
    {D : Finset (Fin n)} (hD : PivotsFromPattern P D) (a b : Fin n) :
    PivotsFromPattern (insert (a, b) P) (insert a D) := by
  intro r hr
  rcases Finset.mem_insert.mp hr with rfl | hr
  · exact ⟨b, Finset.mem_insert_self _ _⟩
  · obtain ⟨s, hs⟩ := hD r hr
    exact ⟨s, Finset.mem_insert_of_mem hs⟩

theorem exists_complete_elimination_chain (n : ℕ) :
    ∃ c : EliminationChain (∅ : Finset (Fin n × Fin n)) ∅,
      c.finalEntries = allPositiveRoots n := by
  suffices ∀ m : ℕ, ∀ (P : Finset (Fin n × Fin n)) (D : Finset (Fin n)),
      (allPositiveRoots n \ P).card = m → InitialRootPattern P → PivotsFromPattern P D →
      ∃ c : EliminationChain P D, c.finalEntries = allPositiveRoots n by
    exact this _ ∅ ∅ rfl (by intro p hp; simp at hp) (by intro a ha; simp at ha)
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro P D hcard hP hD
      by_cases hempty : allPositiveRoots n \ P = ∅
      · refine ⟨.done, ?_⟩
        change P = allPositiveRoots n
        apply Finset.Subset.antisymm
        · exact fun p hp => (hP p hp).1
        · exact Finset.sdiff_eq_empty_iff_subset.mp hempty
      · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image (allPositiveRoots n \ P)
          (fun q => toLex q) (Finset.nonempty_iff_ne_empty.mpr hempty)
        have hab : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
        have hnot : p ∉ P := (Finset.mem_sdiff.mp hp).2
        have hless : (allPositiveRoots n \ insert p P).card < m := by
          rw [Finset.sdiff_insert, ← hcard]
          exact Finset.card_erase_lt_of_mem hp
        obtain ⟨c, hc⟩ := ih _ hless (insert p P) (insert p.1 D) rfl
          (initialRootPattern_insert_min hP p hp hmin) (pivotsFromPattern_insert hD p.1 p.2)
        exact ⟨.step p.1 p.2 (ne_of_lt hab)
          (initialRootPattern_stable hP hab hnot)
          (initialRootPattern_pivot_notMem hP hD hab hnot) c, hc⟩

end DukePrimeDegree

end

end OAI
