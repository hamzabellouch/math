import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
variable {D : Type*} [DecidableEq D]

/-- Cutting a cyclic vertex-link immediately before two distinct corners
splits it into exactly the displayed two cyclic lists. Singleton cycles are
retained: they are genuine vertex instances, even though their permutation
is the identity. -/
theorem split_list (a b : D) (l m : List D)
    (h : (a :: l ++ b :: m).Nodup) :
    swap a b * (a :: l ++ b :: m).formPerm =
      (a :: l).formPerm * (b :: m).formPerm := by
  induction l generalizing a with
  | nil => simp [List.formPerm_cons_cons,← mul_assoc]
  | cons x l ih =>
    have hab : a ≠ b := by
      intro he; exact (List.nodup_cons.mp h).1 (by simp [he])
    have hxb : x ≠ b := by
      have hx := (List.nodup_cons.mp (List.nodup_cons.mp h).2).1
      intro he; exact hx (by simp [he])
    have hs : swap a b * swap a x = swap a x * swap x b := by
      ext z
      simp [swap_apply_def]
      split_ifs <;> subst_vars <;> simp_all
    change swap a b * (a :: x :: (l ++ b :: m)).formPerm = _
    have hi := ih x (List.nodup_cons.mp h).2
    simp only [List.cons_append] at hi
    rw [List.formPerm_cons_cons, ← mul_assoc, hs, mul_assoc, hi,
      ← mul_assoc, ← List.formPerm_cons_cons]

section Finite
variable [Fintype D]

/-- Number of darts minus number of vertex cycles, including singleton cycles.
The integer form avoids artificial truncated-subtraction side conditions. -/
def defect (p : Perm D) : ℤ := p.support.card - p.cycleType.card

def cycles (p : Perm D) : ℤ := Fintype.card D - defect p

lemma defect_disjoint {p q : Perm D} (h : p.Disjoint q) :
    defect (p * q) = defect p + defect q := by
  simp only [defect,h.card_support_mul,h.cycleType_mul,Multiset.card_add,Nat.cast_add]
  ring

lemma defect_list (a : D) (l : List D) (h : (a :: l).Nodup) :
    defect (a :: l).formPerm = l.length := by
  cases l with
  | nil => simp [defect]
  | cons b l =>
    have hl : 2 ≤ (a :: b :: l).length := by simp
    have hc := List.isCycle_formPerm h hl
    have hs := List.support_formPerm_of_nodup (a :: b :: l) h (by
      intro x he; have := congrArg List.length he; simp at this)
    rw [defect,hc.cycleType,hs,List.toFinset_card_of_nodup h]
    simp

omit [Fintype D] in
lemma disjoint_lists (l m : List D) (h : l.Disjoint m) :
    l.formPerm.Disjoint m.formPerm := by
  apply disjoint_iff_eq_or_eq.mpr
  intro x
  by_cases hx : x ∈ l
  · right
    exact List.formPerm_apply_of_notMem (fun hm => h hx hm)
  · exact Or.inl (List.formPerm_apply_of_notMem hx)

lemma defect_split_list (a b : D) (l m : List D)
    (h : (a :: l ++ b :: m).Nodup) :
    defect (swap a b * (a :: l ++ b :: m).formPerm) + 1 =
      defect (a :: l ++ b :: m).formPerm := by
  have hs : ((a::l) ++ (b::m)).Nodup := h
  have hd : (a::l).Disjoint (b::m) := by
    intro x hx hm
    exact (List.nodup_append.mp hs).2.2 x hx x hm rfl
  rw [split_list a b l m h,defect_disjoint (disjoint_lists _ _ hd),
    defect_list a l hs.of_append_left,defect_list b m hs.of_append_right]
  have ho := defect_list a (l ++ b :: m) (by simpa only [List.cons_append] using h)
  simp only [List.cons_append] at ⊢
  rw [ho]
  simp only [List.length_append,List.length_cons,Nat.cast_add,Nat.cast_one]
  ring

lemma remainder_disjoint (p : Perm D) (a : D) :
    (p.cycleOf a).Disjoint ((p.cycleOf a)⁻¹ * p) := by
  apply disjoint_iff_eq_or_eq.mpr
  intro x
  by_cases hx : p.SameCycle a x
  · right
    have he : p.cycleOf a x = p x := by simp [cycleOf_apply,hx]
    change (p.cycleOf a).symm (p x) = x
    rw [← he]
    exact (p.cycleOf a).symm_apply_apply x
  · left
    simp [cycleOf_apply,hx]

/-- A transposition between two corners of one vertex splits that vertex.
This includes the extremal cut creating one or two valence-one vertices. -/
theorem cycles_split (p : Perm D) {a b : D} (hab : a ≠ b)
    (hsame : p.SameCycle a b) : cycles (swap a b * p) = cycles p + 1 := by
  have ha : a ∈ p.support := by
    apply mem_support.mpr
    intro h
    exact hab (hsame.eq_of_left h)
  have hb : b ∈ p.toList a := mem_toList_iff.mpr ⟨hsame,ha⟩
  obtain ⟨l,hl⟩ : ∃ l, p.toList a = a :: l := by
    have hn := p.length_toList_pos_of_mem_support a ha
    cases ht : p.toList a with
    | nil => simp [ht] at hn
    | cons x l =>
      have hx := p.toList_getElem_zero a ha
      simp only [ht,List.getElem_cons_zero] at hx
      exact ⟨l,by simp only [hx]⟩
  have hbl : b ∈ l := by simpa only [hl,List.mem_cons,hab.symm,false_or] using hb
  obtain ⟨l₁,l₂,he⟩ := List.mem_iff_append.mp hbl
  subst l
  have hc : p.cycleOf a = (a :: l₁ ++ b :: l₂).formPerm := by
    rw [← p.formPerm_toList a,hl]
    rfl
  have hn : (a :: l₁ ++ b :: l₂).Nodup := by
    have := p.nodup_toList a
    simpa only [hl,List.cons_append] using this
  have hd := remainder_disjoint p a
  have hh : (swap a b).Disjoint ((p.cycleOf a)⁻¹ * p) := by
    apply disjoint_iff_eq_or_eq.mpr
    intro x
    by_cases hx : x = a ∨ x = b
    · right
      have hxm : x ∈ (p.cycleOf a).support := by
        rcases hx with rfl | rfl
        · exact mem_support_cycleOf_iff.mpr ⟨SameCycle.rfl,ha⟩
        · exact mem_support_cycleOf_iff.mpr ⟨hsame,ha⟩
      exact (disjoint_iff_eq_or_eq.mp hd x).resolve_left (mem_support.mp hxm)
    · left
      exact swap_apply_of_ne_of_ne (by tauto) (by tauto)
  have hnew := hh.mul_left hd
  have hfac : p.cycleOf a * ((p.cycleOf a)⁻¹ * p) = p := by group
  have heq : swap a b * p = (swap a b * p.cycleOf a) * ((p.cycleOf a)⁻¹ * p) := by
    rw [mul_assoc,hfac]
  have ho := defect_disjoint hd
  have hs := defect_split_list a b l₁ l₂ hn
  rw [← hc] at hs
  rw [hfac] at ho
  unfold cycles
  rw [heq,defect_disjoint hnew]
  omega

/-- A cut between two different vertex cycles joins them. The finite
intersection argument handles fixed points without excluding empty links. -/
lemma sameCycle_after_swap (p : Perm D) {a b : D}
    (h : ¬ p.SameCycle a b) : (swap a b * p).SameCycle a b := by
  by_contra hn
  let q := swap a b * p
  have hab : a ≠ b := fun he => h (he.sameCycle p)
  have hp : ∀ x, p.SameCycle a x ∧ q.SameCycle a x →
      p x ≠ a ∧ p x ≠ b ∧ q x = p x := by
    intro x hx
    have hb : p x ≠ b := fun he => h (he ▸ hx.1.apply_right)
    have ha : p x ≠ a := by
      intro he
      have hh := hx.2.apply_right
      have heq : q x = b := by simp [q,mul_apply,he]
      rw [heq] at hh
      exact hn hh
    exact ⟨ha,hb,by simp [q,mul_apply,swap_apply_of_ne_of_ne ha hb]⟩
  let U := {x : D // p.SameCycle a x ∧ q.SameCycle a x}
  let f : U → U := fun x => ⟨p x.val, x.property.1.apply_right,
    by rw [← (hp x.val x.property).2.2]; exact x.property.2.apply_right⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact p.injective (congrArg Subtype.val he)
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hf
  obtain ⟨x,hx⟩ := hsurj ⟨a,SameCycle.rfl,SameCycle.rfl⟩
  exact (hp x.val x.property).1 (congrArg Subtype.val hx)

theorem cycles_merge (p : Perm D) {a b : D}
    (h : ¬ p.SameCycle a b) : cycles (swap a b * p) + 1 = cycles p := by
  have hab : a ≠ b := fun he => h (he.sameCycle p)
  have hs := cycles_split (swap a b * p) hab (sameCycle_after_swap p h)
  simpa only [← mul_assoc,swap_mul_self,one_mul] using hs.symm

/-- Right multiplication cuts the outgoing ends instead of the incoming ends. -/
theorem cycles_split_right (p : Perm D) {a b : D} (hab : a ≠ b)
    (h : p.SameCycle a b) : cycles (p * swap a b) = cycles p + 1 := by
  rw [mul_swap_eq_swap_mul]
  exact cycles_split p (p.injective.ne hab) (h.apply_left.apply_right)

theorem cycles_merge_right (p : Perm D) {a b : D}
    (h : ¬ p.SameCycle a b) : cycles (p * swap a b) + 1 = cycles p := by
  rw [mul_swap_eq_swap_mul]
  apply cycles_merge
  simpa only [sameCycle_apply_left,sameCycle_apply_right] using h

lemma cycles_eq_fixed_add (p : Perm D) :
    cycles p = Fintype.card (Function.fixedPoints p) + p.cycleType.card := by
  have hs : p.support.card ≤ Fintype.card D := p.support.card_le_univ
  rw [Equiv.Perm.card_fixedPoints,p.sum_cycleType]
  simp only [cycles,defect,Nat.cast_sub hs]
  ring

omit [DecidableEq D] in
/-- Agreement on a whole old cycle determines the new cycle, in both
 directions. Finiteness is used only to replace integer powers by naturals. -/
lemma sameCycle_agree (p q : Perm D) (x : D)
    (h : ∀ y, p.SameCycle x y → q y = p y) (y : D) :
    q.SameCycle x y ↔ p.SameCycle x y := by
  have hp : ∀ n : ℕ, (q ^ n) x = (p ^ n) x := by
    intro n; induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ',mul_apply,ih]
      exact h _ (SameCycle.rfl.pow_right)
  constructor <;> intro he
  · obtain ⟨n,hn⟩ := he.exists_nat_pow_eq
    exact ⟨n,by simpa only [zpow_natCast,hp n] using hn⟩
  · obtain ⟨n,hn⟩ := he.exists_nat_pow_eq
    exact ⟨n,by simpa only [zpow_natCast,hp n] using hn⟩

lemma sameCycle_right_swap_away (p : Perm D) {a b x y : D}
    (ha : ¬ p.SameCycle x a) (hb : ¬ p.SameCycle x b) :
    (p * swap a b).SameCycle x y ↔ p.SameCycle x y := by
  apply sameCycle_agree
  intro z hz
  have hza : z ≠ a := fun he => ha (he ▸ hz)
  have hzb : z ≠ b := fun he => hb (he ▸ hz)
  simp only [mul_apply,swap_apply_of_ne_of_ne hza hzb]

lemma notSameCycle_after_split (p : Perm D) {a b : D} (hab : a ≠ b)
    (h : p.SameCycle a b) : ¬ (swap a b * p).SameCycle a b := by
  intro hn
  have h1 := cycles_split p hab h
  have h2 := cycles_split (swap a b * p) hab hn
  simp only [← mul_assoc,swap_mul_self,one_mul] at h2
  omega

end Finite
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
