import OAI.GroupTheory.Kervaire.Annulus

namespace OAI

namespace KervaireRibbon

section
open Monoid Multiplicative
variable {A : Type*} [Group A]

def syllableEval (l : List (ℤ × A)) : FreeProd A :=
  (l.map (fun x ↦ Coprod.inr (ofAdd x.1)*Coprod.inl x.2)).prod

def UnitSyllables (l : List (ℤ × A)) : Prop := ∀ x ∈ l, x.1=1 ∨ x.1 = -1

def Normalized (w : FreeProd A) : Prop :=
  ∃ g : A, ∃ l : List (ℤ × A), UnitSyllables l ∧ w = Coprod.inl g*syllableEval l

lemma Normalized.one : Normalized (1 : FreeProd A) :=
  ⟨1,[],by simp [UnitSyllables],by simp [syllableEval]⟩

lemma Normalized.prependCoefficient {w : FreeProd A} (h : Normalized w) (g : A) :
    Normalized (Coprod.inl g*w) := by
  obtain ⟨a,l,hl,rfl⟩ := h
  exact ⟨g*a,l,hl,by simp only [map_mul,mul_assoc]⟩

lemma Normalized.prependLetter {w : FreeProd A} (h : Normalized w) (n : ℤ)
    (hn : n=1 ∨ n = -1) : Normalized (Coprod.inr (ofAdd n)*w) := by
  obtain ⟨a,l,hl,rfl⟩ := h
  refine ⟨1,(n,a)::l,?_,?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hn
    · exact hl x hx
  · simp only [map_one,one_mul,syllableEval,List.map_cons,List.prod_cons,mul_assoc]

lemma Normalized.prependPower {w : FreeProd A} (h : Normalized w) (n : ℤ) :
    Normalized (Coprod.inr (ofAdd n)*w) := by
  induction n using Int.induction_on with
  | zero => simpa using h
  | succ n ih =>
    have hh := ih.prependLetter 1 (Or.inl rfl)
    convert hh using 1
    rw [add_comm,ofAdd_add,map_mul,mul_assoc]
  | pred n ih =>
    have hh := ih.prependLetter (-1) (Or.inr rfl)
    convert hh using 1
    rw [sub_eq_add_neg,add_comm,ofAdd_add,map_mul,mul_assoc]

lemma normalized_every (w : FreeProd A) : Normalized w := by
  induction w using Coprod.induction_on' with
  | one => exact Normalized.one
  | inl_mul g w ih => exact ih.prependCoefficient g
  | inr_mul n w ih => exact ih.prependPower (toAdd n)

/-- Inserting the actually trivial pair t·t⁻¹ absorbs the leading coefficient.
This is equality in the unchanged free product, not a new group relation. -/
lemma unit_syllables_every (w : FreeProd A) :
    ∃ l : List (ℤ × A), 2 ≤ l.length ∧ UnitSyllables l ∧ syllableEval l = w := by
  obtain ⟨g,l,hl,rfl⟩ := normalized_every w
  refine ⟨(1,1)::(-1,g)::l,by simp,?_,?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inl rfl
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr rfl
      · exact hl x hx
  · simp only [syllableEval,List.map_cons,List.prod_cons,map_one,mul_one,
      ofAdd_neg,map_inv]
    group

lemma syllableEval_exponent (l : List (ℤ × A)) :
    toAdd (Coprod.snd (syllableEval l)) = (l.map Prod.fst).sum := by
  induction l with
  | nil => simp [syllableEval]
  | cons x l ih =>
    simp only [syllableEval,List.map_cons,List.prod_cons] at ih ⊢
    simpa using congrArg (fun n : ℤ ↦ x.1+n) ih
end

open Equiv Equiv.Perm
open scoped Classical
variable {I : Type*} [DecidableEq I]

lemma circle_formPerm (i : I) (l : List I) (hn : (i::l).Nodup) :
    Circle (i::l).formPerm i l := by
  change ((i::l)++[i]).IsChain (fun x y ↦ (i::l).formPerm x=y)
  rw [List.isChain_iff_getElem]
  intro n hn'
  have hh : n < (i::l).length := by simp only [List.length_append,List.length_singleton] at hn'; omega
  rw [List.getElem_append_left hh]
  by_cases hs : n+1 < (i::l).length
  · rw [List.getElem_append_left hs]
    exact List.formPerm_apply_lt_getElem _ hn n hs
  · have he : n = l.length := by simp only [List.length_cons] at hh hs; omega
    subst n
    simp only [List.getElem_append_right (by simp : (i::l).length ≤ l.length+1),
      List.length_cons,Nat.sub_self,List.getElem_cons_zero]
    exact List.formPerm_apply_getElem_length i l

lemma formPerm_sameCycle_all [Finite I] (i : I) (l : List I) (hn : (i::l).Nodup)
    (hcover : ∀ j, j ∈ i::l) : ∀ j k, (i::l).formPerm.SameCycle j k := by
  intro j k
  have hc := circle_formPerm i l hn
  exact ((circle_cycles _ i l hc j).mpr (hcover j)).symm.trans
    ((circle_cycles _ i l hc k).mpr (hcover k))
end KervaireRibbon

end OAI
