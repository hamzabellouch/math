import OAI.GroupTheory.PolycyclicRecognition.Algebra.CayleyWordLength

namespace OAI

/-! # Word balls under homomorphisms

Image word balls are literal finite images, so polynomial growth descends to
the matrix image constructed by the harmonic argument.
-/
namespace PolycyclicRecognition
variable {G H : Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H]

theorem wordBall_image (f : G →* H) (S : Finset G) (n : ℕ) :
    wordBall (S.image f) n = (wordBall S n).image f := by
  have hlift (l : List H) (hl : ∀ t ∈ l, t ∈ S.image f) :
      ∃ k : List G, k.length = l.length ∧ (∀ s ∈ k, s ∈ S) ∧ k.map f = l := by
    induction l with
    | nil => exact ⟨[], rfl, by simp, rfl⟩
    | cons t l ih =>
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (hl t (List.mem_cons_self ..))
      obtain ⟨k, hk, hkS, he⟩ := ih (fun t ht => hl t (List.mem_cons_of_mem _ ht))
      refine ⟨s :: k, by simpa using hk, ?_, by simp [he]⟩
      intro u hu
      exact (List.mem_cons.mp hu).elim (fun h => h ▸ hs) (hkS u)
  ext y
  constructor
  · intro hy
    obtain ⟨l, hl, hS, rfl⟩ := (mem_wordBall_iff (S.image f) n y).mp hy
    obtain ⟨k, hk, hkS, he⟩ := hlift l hS
    apply Finset.mem_image.mpr
    refine ⟨k.prod, (mem_wordBall_iff S n _).mpr ⟨k, hk.trans_le hl, hkS, rfl⟩, ?_⟩
    rw [map_list_prod, he]
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨l, hl, hS, rfl⟩ := (mem_wordBall_iff S n x).mp hx
    apply (mem_wordBall_iff (S.image f) n _).mpr
    refine ⟨l.map f, by simpa using hl, ?_, ?_⟩
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      exact Finset.mem_image.mpr ⟨s, hS s hs, rfl⟩
    · exact (map_list_prod f l).symm

theorem wordBall_image_card_le (f : G →* H) (S : Finset G) (n : ℕ) :
    (wordBall (S.image f) n).card ≤ (wordBall S n).card := by
  rw [wordBall_image]
  exact Finset.card_image_le

theorem wordBall_hom_mem_scaled (f : G →* H) (S : Finset H)
    (T : Finset G) (m : ℕ) (hT : ∀ t ∈ T, f t ∈ wordBall S m)
    (n : ℕ) {g : G} (hg : g ∈ wordBall T n) : f g ∈ wordBall S (m * n) := by
  have hlist (l : List G) (hl : ∀ t ∈ l, t ∈ T) :
      f l.prod ∈ wordBall S (m * l.length) := by
    induction l with
    | nil => simp
    | cons t l ih =>
      rw [List.prod_cons, map_mul]
      have h := mul_mem_wordBall (hT t (hl t (List.mem_cons_self ..)))
        (ih (fun s hs => hl s (List.mem_cons_of_mem _ hs)))
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm] using h
  obtain ⟨l, hl, hS, rfl⟩ := (mem_wordBall_iff T n g).mp hg
  exact wordBall_mono S (Nat.mul_le_mul_left m hl) (hlist l hS)

end PolycyclicRecognition

end OAI
