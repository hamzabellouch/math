import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupFiniteWordBalls

namespace OAI
noncomputable section
namespace CuntzPureness
local instance freeGroupPowersPartitionDecidableEq {X : Type*} : DecidableEq X :=
  Classical.decEq X

def freeGroupPowersC (n : ℕ) : Set (FreeGroup ℕ) :=
  {g | ∃ p l, g.toWord = p::l ∧ n ≤ p.1}

lemma reduced_append_of_old_new (n : ℕ) (l : List (ℕ × Bool))
    (p : ℕ × Bool) (r : List (ℕ × Bool))
    (hl : FreeGroup.IsReduced l) (hr : FreeGroup.IsReduced (p::r))
    (hb : ∀ q ∈ l, q.1 < n) (hp : n ≤ p.1) :
    FreeGroup.IsReduced (l ++ p::r) := by
  apply List.IsChain.append hl hr
  intro q hq t ht he
  have ht' : t = p := by simpa [eq_comm] using ht
  subst t
  have hqn := hb q (List.mem_of_mem_getLast? hq)
  omega

lemma freeGroup_old_mul_new_word (n : ℕ) (g h : FreeGroup ℕ)
    (hg : g ∈ initialFreeSubgroup n) (hh : h ∈ freeGroupPowersC n) :
    (g*h).toWord = g.toWord ++ h.toWord := by
  obtain ⟨p,r,he,hp⟩ := hh
  rw [FreeGroup.toWord_mul]
  apply FreeGroup.IsReduced.reduce_eq
  rw [he]
  exact reduced_append_of_old_new n _ p r FreeGroup.isReduced_toWord
    (he ▸ FreeGroup.isReduced_toWord) (initialFreeSubgroup_word_bound n g hg) hp

theorem freeGroupPowersC_old_disjoint (n : ℕ) (g : FreeGroup ℕ)
    (hg : g ∈ initialFreeSubgroup n) (hg1 : g ≠ 1)
    (h : FreeGroup ℕ) (hh : h ∈ freeGroupPowersC n) :
    g*h ∉ freeGroupPowersC n := by
  have hw := freeGroup_old_mul_new_word n g h hg hh
  have hn : g.toWord ≠ [] := by
    intro he
    apply hg1
    exact FreeGroup.toWord_injective (he.trans FreeGroup.toWord_one.symm)
  obtain ⟨q,l,hq⟩ := List.exists_cons_of_ne_nil hn
  intro hm
  obtain ⟨p,r,hp,hpn⟩ := hm
  rw [hw,hq,List.cons_append] at hp
  have he : q = p := (List.cons.inj hp).1
  subst p
  have hqn := initialFreeSubgroup_word_bound n g hg q (by rw [hq]; exact List.mem_cons_self)
  omega

lemma freeGroup_fresh_mul_complement_word (n k : ℕ) (hk : n ≤ k)
    (g : FreeGroup ℕ) (hg : g ∉ freeGroupPowersC n) :
    (FreeGroup.of k*g).toWord = (k,true)::g.toWord := by
  rw [FreeGroup.toWord_mul,FreeGroup.toWord_of,List.singleton_append]
  apply FreeGroup.IsReduced.reduce_eq
  cases he : g.toWord with
  | nil => exact FreeGroup.IsReduced.singleton
  | cons p l =>
    apply FreeGroup.isReduced_cons_cons.mpr
    refine ⟨?_, he ▸ FreeGroup.isReduced_toWord⟩
    intro hkp
    have hpn : ¬ n ≤ p.1 := fun hp => hg ⟨p,l,he,hp⟩
    omega

theorem freeGroupPowers_complement_images_disjoint (n k j : ℕ)
    (hk : n ≤ k) (hj : n ≤ j) (hkj : k ≠ j) :
    Disjoint ((fun g => FreeGroup.of k*g) '' (freeGroupPowersC n)ᶜ)
      ((fun g => FreeGroup.of j*g) '' (freeGroupPowersC n)ᶜ) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨g,hg,rfl⟩ ⟨h,hh,he⟩
  have hw := congrArg FreeGroup.toWord he
  rw [freeGroup_fresh_mul_complement_word n j hj h hh,
    freeGroup_fresh_mul_complement_word n k hk g hg] at hw
  exact hkj (congrArg Prod.fst (List.cons.inj hw).1).symm
end CuntzPureness

end

end OAI
