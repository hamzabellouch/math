import Mathlib
import OAI.Computability.FiniteCompiler.Quotients
import OAI.GroupTheory.SimpleOvergroups.ContextualTables

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes.Bootstrap Relation

namespace DelimiterCode
variable {A B S : Type*}

def alphabet (C : DelimiterCode A S) : Set S :=
  {s | s = C.start ∨ s = C.stop ∨ ∃ a, s ∈ C.body a}

theorem mem_alphabet_of_mem_encode (C : DelimiterCode A S) {s : S} {w : List A}
    (hs : s ∈ C.encode w) : s ∈ C.alphabet := by
  obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hs
  simp only [block, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨a, h⟩)
  · exact Or.inr (Or.inl h)

theorem avoids_of_not_mem_alphabet (C : DelimiterCode A S) {s : S}
    (hs : s ∉ C.alphabet) (w : List A) : s ∉ C.encode w :=
  fun h => hs (C.mem_alphabet_of_mem_encode h)

theorem disjoint_infix (C : DelimiterCode A S) (D : DelimiterCode B S)
    (hd : Disjoint C.alphabet D.alphabet) {u : List A} {v : List B}
    (hv : v ≠ []) (he : D.encode v <:+: C.encode u) : False := by
  have hn : D.encode v ≠ [] := fun h => hv ((D.encode_eq_nil _).mp h)
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hn
  exact (Set.disjoint_left.mp hd) (C.mem_alphabet_of_mem_encode (he.subset hs))
    (D.mem_alphabet_of_mem_encode hs)

theorem disjoint_overlap (C : DelimiterCode A S) (D : DelimiterCode B S)
    (hd : Disjoint C.alphabet D.alphabet) {u : List A} {v : List B} {p m q : List S}
    (hm : m ≠ []) (he : C.encode u = p++m) (hf : D.encode v = m++q) : False := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hm
  exact (Set.disjoint_left.mp hd)
    (C.mem_alphabet_of_mem_encode (by rw [he]; exact List.mem_append_right _ hs))
    (D.mem_alphabet_of_mem_encode (by rw [hf]; exact List.mem_append_left _ hs))
end DelimiterCode

namespace Families
variable {I S : Type*} {A Q : I → Type*} [Fintype I] [Fintype S]
variable {r : S → S → Prop} [Std.Trichotomous r]
variable (C : ∀ i, DelimiterCode (A i) S) (E : ∀ i, FiniteSearch (C i))
  (wf : WellFounded r) (q : ∀ i, List (A i) → Option (Q i)) (z : S)

noncomputable def table (n : ℕ) : List (List S × List S) :=
  Base.absorption z ++ (Static.letters I).flatMap (fun i => CodeTable.table (C i) (E i) wf (q i) z n)

omit [Std.Trichotomous r] in
theorem mem_table [Std.Trichotomous r] {n : ℕ} {p : List S × List S} : p ∈ table C E wf q z n ↔
    p ∈ Base.absorption z ∨ ∃ i, p ∈ CodeTable.table (C i) (E i) wf (q i) z n := by
  classical
  simp [table, Static.letters]

theorem absorbs (n : ℕ) : Absorbs (table C E wf q z n) z := by
  classical
  intro a
  constructor <;> apply (mem_table C E wf q z).mpr <;> apply Or.inl <;>
    apply (Base.mem_absorption z).mpr
  · exact ⟨a, Or.inl rfl, rfl⟩
  · exact ⟨a, Or.inr rfl, rfl⟩

theorem preserves_zero (hz : ∀ i, z ∉ (C i).alphabet) (n : ℕ) :
    ∀ p ∈ table C E wf q z n, z ∈ p.1 → z ∈ p.2 := by
  classical
  intro ⟨u,v⟩ hp hu
  rcases (mem_table C E wf q z).mp hp with hp | ⟨i,hp⟩
  · obtain ⟨a,_,rfl⟩ := (Base.mem_absorption z).mp hp
    simp
  · obtain ⟨w,_,_,_,rfl,_⟩ := (CodeTable.mem_table (C i) (E i) wf (q i) z).mp hp
    exact ((hz i) ((C i).mem_alphabet_of_mem_encode hu)).elim

theorem critical (hz : ∀ i, z ∉ (C i).alphabet)
    (hd : ∀ i j, i ≠ j → Disjoint (C i).alphabet (C j).alphabet) {n : ℕ}
    (hzero : ∀ i, q i [] ≠ none)
    (hc : ∀ i, CodeTable.Contextual (C i) (q i) n)
    (hi : ∀ i, CodeTable.ZeroIdeal (C i) (q i) n) : Critical (table C E wf q z n) n := by
  classical
  let rs := table C E wf q z n
  have hza : Absorbs rs z := absorbs C E wf q z n
  have hp := preserves_zero C E wf q z hz n
  have ht (i) : ∀ p ∈ CodeTable.table (C i) (E i) wf (q i) z n, p ∈ rs :=
    fun _ h => (mem_table C E wf q z).mpr (.inr ⟨i,h⟩)
  have hzeroPeak {w u v : List S} (hw : z ∈ w) (hu : Step rs w u) (hv : Step rs w v) :
      Join (Steps rs) u v :=
    ⟨[z], absorbs_mem hza (step_preserves_letter hp hw hu),
      absorbs_mem hza (step_preserves_letter hp hw hv)⟩
  have hnabs {u v : List S} (h : z ∉ u) : (u,v) ∉ Base.absorption z := by
    intro hh
    obtain ⟨a,ha,_⟩ := (Base.mem_absorption z).mp hh
    rcases ha with rfl | rfl <;> simp at h
  constructor
  · intro u u' v v' hu hv x y he hlen
    by_cases huz : z ∈ u
    · apply hzeroPeak huz
      · simpa using Step.apply hu [] []
      · simpa only [he] using Step.apply hv x y
    have hvz : z ∉ v := fun hh => huz (by simp [he,hh])
    have hut := (mem_table C E wf q z).mp hu
    have hvt := (mem_table C E wf q z).mp hv
    simp only [hnabs huz, hnabs hvz, false_or] at hut hvt
    obtain ⟨i,hui⟩ := hut
    obtain ⟨j,hvj⟩ := hvt
    by_cases hij : i = j
    · subst j
      exact CodeTable.critical_containment (C i) (E i) wf (q i) z
        (hzero i) hza (ht i) (hc i) (hi i) hui hvj he hlen
    · obtain ⟨a,_,_,_,rfl,_⟩ := (CodeTable.mem_table (C i) (E i) wf (q i) z).mp hui
      obtain ⟨b,_,hb,_,rfl,_⟩ := (CodeTable.mem_table (C j) (E j) wf (q j) z).mp hvj
      exact ((C i).disjoint_infix (C j) (hd i j hij) hb ⟨x,y,he.symm⟩).elim
  · intro u u' v v' hu hv p m t hm he hh hlen
    by_cases hwz : z ∈ p++m++t
    · apply hzeroPeak hwz
      · simpa only [he, List.nil_append, List.append_assoc] using Step.apply hu [] t
      · simpa only [hh, List.append_nil, List.append_assoc] using Step.apply hv p []
    have huz : z ∉ u := fun h => hwz (by simp [←he,h])
    have hvz : z ∉ v := fun h => hwz (by simpa only [List.append_assoc,←hh,List.mem_append] using Or.inr h)
    have hut := (mem_table C E wf q z).mp hu
    have hvt := (mem_table C E wf q z).mp hv
    simp only [hnabs huz, hnabs hvz, false_or] at hut hvt
    obtain ⟨i,hui⟩ := hut
    obtain ⟨j,hvj⟩ := hvt
    by_cases hij : i = j
    · subst j
      exact CodeTable.critical_overlap (C i) (E i) wf (q i) z
        (hzero i) hza (ht i) (hc i) (hi i) hui hvj hm he hh hlen
    · obtain ⟨a,_,_,_,rfl,_⟩ := (CodeTable.mem_table (C i) (E i) wf (q i) z).mp hui
      obtain ⟨b,_,_,_,rfl,_⟩ := (CodeTable.mem_table (C j) (E j) wf (q j) z).mp hvj
      exact ((C i).disjoint_overlap (C j) (hd i j hij) hm he hh).elim

theorem decreasing (n : ℕ) : ∀ p ∈ table C E wf q z n, List.Shortlex r p.2 p.1 := by
  classical
  intro ⟨u,v⟩ hp
  rcases (mem_table C E wf q z).mp hp with hp | ⟨i,hp⟩
  · obtain ⟨a,ha,rfl⟩ := (Base.mem_absorption z).mp hp
    rcases ha with rfl | rfl <;> exact List.Shortlex.of_length_lt (by simp)
  · exact CodeTable.decreasing (C i) (E i) wf (q i) z n (u,v) hp

theorem stable {k n : ℕ} (hkn : k ≤ n) :
    Selectors.BoundedEq (table C E wf q z k) (table C E wf q z n) k := by
  intro p hp
  simp only [mem_table]
  exact or_congr Iff.rfl (exists_congr (fun i => CodeTable.stable (C i) (E i) wf (q i) z hkn p hp))

theorem good_at (hz : ∀ i, z ∉ (C i).alphabet)
    (hd : ∀ i j, i ≠ j → Disjoint (C i).alphabet (C j).alphabet) {n : ℕ}
    (hzero : ∀ i, q i [] ≠ none)
    (hc : ∀ i, CodeTable.Contextual (C i) (q i) n)
    (hi : ∀ i, CodeTable.ZeroIdeal (C i) (q i) n) :
    GoodTable (r := r) (fun n => Part.some (table C E wf q z n)) n :=
  ⟨_, Part.mem_some_iff.mpr rfl, decreasing C E wf q z n,
    critical C E wf q z hz hd hzero hc hi⟩
end Families
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
