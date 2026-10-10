import OAI.GroupTheory.PolycyclicRecognition.Analysis.Packing

namespace OAI

/-! # Products, inverses and finite paths in the intrinsic word balls -/
namespace PolycyclicRecognition
variable {G : Type*} [Group G] [DecidableEq G]

theorem wordBall_mono (S : Finset G) : Monotone (wordBall S) := by
  intro m n hmn g hg
  obtain ⟨l, hl, hs, hp⟩ := (mem_wordBall_iff S m g).mp hg
  exact (mem_wordBall_iff S n g).mpr ⟨l, hl.trans hmn, hs, hp⟩

theorem mul_mem_wordBall {S : Finset G} {m n : ℕ} {g h : G}
    (hg : g ∈ wordBall S m) (hh : h ∈ wordBall S n) :
    g * h ∈ wordBall S (m + n) := by
  obtain ⟨l, hl, hs, rfl⟩ := (mem_wordBall_iff S m g).mp hg
  obtain ⟨k, hk, ht, rfl⟩ := (mem_wordBall_iff S n h).mp hh
  apply (mem_wordBall_iff S (m + n) _).mpr
  refine ⟨l ++ k, by simpa only [List.length_append] using Nat.add_le_add hl hk, ?_, ?_⟩
  · intro s hs'
    exact (List.mem_append.mp hs').elim (hs s) (ht s)
  · exact List.prod_append

theorem inv_mem_wordBall {S : Finset G} (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    {n : ℕ} {g : G} (hg : g ∈ wordBall S n) : g⁻¹ ∈ wordBall S n := by
  obtain ⟨l, hl, hs, rfl⟩ := (mem_wordBall_iff S n g).mp hg
  apply (mem_wordBall_iff S n _).mpr
  refine ⟨(l.map Inv.inv).reverse, by simpa using hl, ?_, ?_⟩
  · intro s hs'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hs')
    exact hS t (hs t ht)
  · exact (List.prod_inv_reverse l).symm

theorem word_prefix_mem_wordBall {S : Finset G} {l : List G}
    (hl : ∀ s ∈ l, s ∈ S) (i : ℕ) : (l.take i).prod ∈ wordBall S i := by
  exact (mem_wordBall_iff S i _).mpr
    ⟨l.take i, List.length_take_le _ _, fun s hs => hl s (List.mem_of_mem_take hs), rfl⟩

end PolycyclicRecognition

end OAI
