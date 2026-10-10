import Mathlib
import OAI.Analysis.Commutator.FiniteWordTelescoping
import OAI.Analysis.Commutator.PartialUnitaryAlgebra

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.FinitePatching

namespace Words

variable {A J K : Type*} [CStarAlgebra A]

abbrev Slot (K : Type*) := Option (Option K)

abbrev Letter (J K : Type*) := J × Slot K

def NonzeroSlot (s : Slot K) : Prop := ∃ k,s=some (some k)

def Valid (l : List (Letter J K)) : Prop :=
  ∀ s i t,l=s++i::t → t≠[] → NonzeroSlot i.2

lemma valid_of_internal (s : List (Letter J K)) (i : Letter J K)
    (hs : ∀ j∈s,NonzeroSlot j.2) : Valid (s++[i]) := by
  revert hs
  induction s with
  | nil =>
    intro hs a b c he hc
    have hlen := congrArg List.length he
    simp only [List.nil_append,List.length_cons,List.length_nil,List.length_append] at hlen
    have hcl : 0<c.length := List.length_pos_iff.mpr hc
    omega
  | cons j s ih =>
    intro hs a b c he hc
    cases a with
    | nil =>
      have hh := List.cons.inj he
      have hb : j=b := hh.1
      subst b
      exact hs j (by simp)
    | cons a t =>
      have hh := List.cons.inj he
      exact ih (fun z hz => hs z (by simp [hz])) t b c hh.2 hc

lemma internal_prefix {l s t : List (Letter J K)} {i : Letter J K}
    (hv : Valid l) (he : l=s++i::t) : ∀ j∈s,NonzeroSlot j.2 := by
  intro j hj
  obtain ⟨a,b,rfl⟩ := List.mem_iff_append.mp hj
  apply hv a j (b++i::t)
  · simpa only [List.append_assoc,List.cons_append] using he
  · simp

lemma internal_middle {l s t r : List (Letter J K)} {i j : Letter J K}
    (hv : Valid l) (he : l=s++i::(t++j::r)) : ∀ b∈t,NonzeroSlot b.2 := by
  intro b hb
  have hp := internal_prefix hv (show l=(s++[i]++t)++j::r by
    simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using he)
  exact hp b (by simp [hb])

lemma tail_nil_of_not_nonzero {l s t : List (Letter J K)} {i : Letter J K}
    (hv : Valid l) (he : l=s++i::t) (hi : ¬NonzeroSlot i.2) : t=[] := by
  by_contra ht
  exact hi (hv s i t he ht)

variable (x : J → A) (k : K → ℤ)

def slotPower (v : PartialUnitary A) : Slot K → A
  | none => 1
  | some none => v.support
  | some (some i) => v.power (k i)

def slotIncrement (w : PartialUnitary A) : Slot K → A
  | none => 0
  | some none => w.support
  | some (some i) => w.power (k i)

def letter (v : PartialUnitary A) (i : Letter J K) : A := x i.1*slotPower k v i.2

def newLetter (w : PartialUnitary A) (i : Letter J K) : A := x i.1*slotIncrement k w i.2

def word (v : PartialUnitary A) (l : List (Letter J K)) : A := wordProduct (letter x k v) l

@[simp] lemma word_nil (v : PartialUnitary A) : word x k v []=1 := rfl

@[simp] lemma word_cons (v : PartialUnitary A) (i : Letter J K) (l : List (Letter J K)) :
    word x k v (i::l)=letter x k v i*word x k v l := rfl

lemma word_append (v : PartialUnitary A) (s t : List (Letter J K)) :
    word x k v (s++t)=word x k v s*word x k v t := wordProduct_append _ _ _

@[simp] lemma word_open_last (v : PartialUnitary A) (s : List (Letter J K)) (j : J) :
    word x k v (s++[(j,none)])=word x k v s*x j := by
  simp [word_append,letter,slotPower]

@[simp] lemma word_support_last (v : PartialUnitary A) (s : List (Letter J K)) (j : J) :
    word x k v (s++[(j,some none)])=word x k v s*x j*v.support := by
  simp [word_append,letter,slotPower,mul_assoc]

lemma slotPower_norm (v : PartialUnitary A) (s : Slot K) : ‖slotPower k v s‖ ≤ 1 := by
  cases s with
  | none => exact (IsStarProjection.one A).norm_le _
  | some s =>
    cases s with
    | none => exact v.projection.norm_le _
    | some i => exact v.power_norm _

lemma letter_norm (hx : ∀ j,‖x j‖ ≤ 1) (v : PartialUnitary A) (i : Letter J K) :
    ‖letter x k v i‖ ≤ 1 :=
  (_root_.norm_mul_le _ _).trans ((mul_le_mul (hx _) (slotPower_norm k v _)
    (_root_.norm_nonneg _) (by norm_num)).trans_eq (one_mul (1:ℝ)))

lemma word_norm (hx : ∀ j,‖x j‖ ≤ 1) (v : PartialUnitary A) (l : List (Letter J K)) :
    ‖word x k v l‖ ≤ 1 := by
  induction l with
  | nil => exact (IsStarProjection.one A).norm_le _
  | cons i l ih =>
    rw [word_cons]
    exact (_root_.norm_mul_le _ _).trans ((mul_le_mul (letter_norm x k hx v i) ih
      (_root_.norm_nonneg _) (by norm_num)).trans_eq (one_mul (1:ℝ)))

lemma slotPower_add (v w : PartialUnitary A) (h : v.support*w.support=0) (s : Slot K) :
    slotPower k (v.add w h) s=slotPower k v s+slotIncrement k w s := by
  cases s with
  | none => simp [slotPower,slotIncrement]
  | some s =>
    cases s with
    | none => rfl
    | some i => exact v.add_power w h _

lemma letter_add (v w : PartialUnitary A) (h : v.support*w.support=0) (i : Letter J K) :
    letter x k (v.add w h) i=letter x k v i+newLetter x k w i := by
  simp only [letter,newLetter,slotPower_add,mul_add]

lemma word_add (v w : PartialUnitary A) (h : v.support*w.support=0) (l : List (Letter J K)) :
    word x k (v.add w h) l=wordProduct (fun i => letter x k v i+newLetter x k w i) l := by
  unfold word
  congr 1
  funext i
  exact letter_add x k v w h i

end Words

end Kadison.FinitePatching

end

end
end

end OAI
