import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
variable {D : Type*} [DecidableEq D]

lemma involution_swap_sq (p : Perm D) (hp : p * p = 1) (a : D) :
    (swap a (p a) * p) * (swap a (p a) * p) = 1 := by
  have haa : p (p a) = a := congrArg (fun q : Perm D => q a) hp
  have hc : p * swap a (p a) = swap a (p a) * p := by
    rw [mul_swap_eq_swap_mul,haa,swap_comm (p a) a]
  calc
    _ = swap a (p a) * (p * swap a (p a)) * p := by group
    _ = swap a (p a) * (swap a (p a) * p) * p := by rw [hc]
    _ = 1 := by rw [← mul_assoc,swap_mul_self,one_mul,hp]

variable [Fintype D]

lemma involution_swap_support (p : Perm D) (hp : p * p = 1) (a : D) :
    (swap a (p a) * p).support = p.support \ {a,p a} := by
  have hh : ∀ x, p (p x) = x := fun x => congrArg (fun q : Perm D => q x) hp
  ext x
  by_cases ha : x = a
  · subst x; simp
  by_cases hb : x = p a
  · subst x; simp [hh]
  have hpa : p x ≠ a := fun he => hb (by rw [← hh x,he])
  have hpb : p x ≠ p a := p.injective.ne ha
  simp [mem_support,mul_apply,swap_apply_of_ne_of_ne hpa hpb,ha,hb]

lemma involution_swap_card (p : Perm D) (hp : p * p = 1) {a : D} (ha : p a ≠ a) :
    (swap a (p a) * p).support.card + 2 = p.support.card := by
  rw [involution_swap_support p hp]
  have hs : ({a,p a} : Finset D) ⊆ p.support := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x; exact mem_support.mpr ha
    · have he := Finset.mem_singleton.mp hx
      subst x
      have hh : p (p a) = a := congrArg (fun q : Perm D => q a) hp
      exact mem_support.mpr (by rw [hh]; exact ha.symm)
  have hc := Finset.card_sdiff_add_card_eq_card hs
  simpa [ha,ha.symm] using hc

/-- Every finite involution is a product of its actual paired points, with
exactly half the support cardinal many transpositions. -/
theorem involution_pairs (p : Perm D) (hp : p * p = 1) :
    ∃ l : List (D × D),
      (l.map (fun ab => swap ab.1 ab.2)).prod = p ∧
      2 * l.length = p.support.card ∧
      ∀ ab ∈ l, ab.1 ≠ ab.2 ∧ p ab.1 = ab.2 := by
  generalize hn : p.support.card = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases he : p = 1
    · subst p
      exact ⟨[],by simp,by simpa using hn,by simp⟩
    obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr (fun hh => he (support_eq_empty_iff.mp hh))
    have hpa : p a ≠ a := mem_support.mp ha
    let q := swap a (p a) * p
    have hq : q * q = 1 := involution_swap_sq p hp a
    have hlt : q.support.card < n := by
      rw [← hn]
      exact card_support_swap_mul hpa
    obtain ⟨l,hl,hcard,hpairs⟩ := ih q.support.card hlt q hq rfl
    refine ⟨(a,p a)::l,?_,?_,?_⟩
    · simp only [List.map_cons,List.prod_cons]
      rw [hl]
      simp [q,← mul_assoc]
    · have hc := involution_swap_card p hp hpa
      simp only [List.length_cons]
      dsimp only [q] at hcard
      omega
    · intro ab hab
      rcases List.mem_cons.mp hab with rfl | hab
      · exact ⟨hpa.symm,rfl⟩
      obtain ⟨hnab,heab⟩ := hpairs ab hab
      have hmem : ab.1 ∈ q.support := mem_support.mpr (by rw [heab]; exact hnab.symm)
      have houtside : ab.1 ≠ a ∧ ab.1 ≠ p a := by
        change ab.1 ∈ (swap a (p a) * p).support at hmem
        rw [involution_swap_support p hp] at hmem
        simpa only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,not_or] using (Finset.mem_sdiff.mp hmem).2
      have hpp : p (p ab.1) = ab.1 := congrArg (fun q : Perm D => q ab.1) hp
      have hza : p ab.1 ≠ a := fun he => houtside.2 (by rw [← hpp,he])
      have hzb : p ab.1 ≠ p a := p.injective.ne houtside.1
      exact ⟨hnab,by simpa [q,mul_apply,swap_apply_of_ne_of_ne hza hzb] using heab⟩

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
