import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.FramedLen

namespace OAI

namespace IndependentSetsCut.CounterMachine.Expr
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

def Represented (f : List Bool → (ℕ → ℕ) → ℕ) : Prop :=
  ∃ e : Expr, ∀ input args, e.eval input args = f input args

namespace Represented
variable {f g h : List Bool → (ℕ → ℕ) → ℕ}
theorem const (n : ℕ) : Represented (fun _ _ => n) := ⟨.const n, by intros; rfl⟩
theorem arg (k : ℕ) : Represented (fun _ a => a k) := ⟨.arg k, by intros; rfl⟩
theorem word (hf : Represented f) : Represented (fun s a => wordValue s (f s a)) := by
  obtain ⟨e,he⟩ := hf; exact ⟨Expr.word e, by intros; simp [he]⟩
theorem add (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a+g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨.add e d, by intros; simp [eval,he,hd]⟩
theorem sub (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a-g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨.sub e d, by intros; simp [eval,he,hd]⟩
theorem mul (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a*g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨.mul e d, by intros; simp [eval,he,hd]⟩
theorem div (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a/g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨quotient e d, by intros; simp [he,hd]⟩
theorem mod (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a%g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨remainder e d, by intros; simp [he,hd]⟩
theorem pow (hf : Represented f) (n : ℕ) : Represented (fun s a => f s a^n) := by
  obtain ⟨e,he⟩ := hf; exact ⟨power e n, by intros; simp [he]⟩
theorem eq (hf : Represented f) (hg : Represented g) :
    Represented (fun s a => if f s a=g s a then 1 else 0) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨equal e d, by intros; simp [he,hd]⟩
theorem lt (hf : Represented f) (hg : Represented g) :
    Represented (fun s a => if f s a<g s a then 1 else 0) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨Expr.lt e d, by intros; simp [he,hd]⟩
theorem cond (hf : Represented f) (hg : Represented g) (hh : Represented h) :
    Represented (fun s a => if f s a ≠ 0 then g s a else h s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; obtain ⟨c,hc⟩ := hh
  exact ⟨Expr.cond e d c, by intros; simp [he,hd,hc]⟩
theorem sum (hf : Represented f) (hg : Represented g) :
    Represented (fun s a => ∑ i ∈ range (f s a), g s (bind a i)) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg
  exact ⟨.sum e d, by intros; simp [eval,he,hd]⟩
theorem finiteSum {I : Type} [Fintype I] {f : I → List Bool → (ℕ → ℕ) → ℕ}
    (hf : ∀ i, Represented (f i)) : Represented (fun s a => ∑ i, f i s a) := by
  choose e he using hf
  exact ⟨Expr.finiteSum e, by intros; simp [he]⟩
theorem rename (hf : Represented f) (r : ℕ → ℕ) :
    Represented (fun s a => f s (fun k => a (r k))) := by
  obtain ⟨e,he⟩ := hf
  exact ⟨e.rename r, by intros; simp [he]⟩
theorem subst (hf : Represented f) {v : ℕ → List Bool → (ℕ → ℕ) → ℕ}
    (hv : ∀ k, Represented (v k)) : Represented (fun s a => f s (fun k => v k s a)) := by
  obtain ⟨e,he⟩ := hf; choose d hd using hv
  exact ⟨e.subst d, by intros; simp [he,hd]⟩
theorem congr (hf : Represented f) (h : ∀ s a, f s a=g s a) : Represented g := by
  obtain ⟨e,he⟩ := hf; exact ⟨e, fun s a => (he s a).trans (h s a)⟩
end Represented
end IndependentSetsCut.CounterMachine.Expr
namespace IndependentSetsCut.CounterMachine.UnaryTables

section
open scoped BigOperators
open Finset

def offset (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ range n, (f j + 1)

def words (f : ℕ → ℕ) (n : ℕ) : List Bool :=
  ((List.range n).map f).flatMap (fun v => List.replicate v true ++ [false])

lemma offset_succ (f : ℕ → ℕ) (n : ℕ) :
    offset f (n+1) = offset f n + (f n+1) := by simp [offset, sum_range_succ]

lemma offset_mono (f : ℕ → ℕ) : Monotone (offset f) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [offset_succ]
  omega

lemma words_succ (f : ℕ → ℕ) (n : ℕ) :
    words f (n+1) = words f n ++ (List.replicate (f n) true ++ [false]) := by
  simp [words,List.range_succ,List.flatMap_append]

lemma words_length (f : ℕ → ℕ) (n : ℕ) : (words f n).length = offset f n := by
  induction n with
  | zero => simp [words,offset]
  | succ n ih => simp [words_succ,ih,offset_succ]

lemma get_word (v i : ℕ) :
    ((List.replicate v true ++ [false])[i]?).getD false = true ↔ i < v := by
  by_cases h : i < v
  · rw [List.getElem?_append_left (by simpa using h)]
    simp [h]
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt h)]
    simp only [List.length_replicate]
    cases e : i-v with
    | zero => simp [h]
    | succ j => simp [h]

lemma words_bit (f : ℕ → ℕ) (n i : ℕ) :
    ((words f n)[i]?).getD false = true ↔
      ∃ j < n, offset f j ≤ i ∧ i < offset f j + f j := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    rw [words_succ]
    by_cases h : i < offset f n
    · rw [List.getElem?_append_left (by simpa [words_length] using h),ih]
      constructor
      · rintro ⟨j,hj,hl,hu⟩; exact ⟨j,Nat.lt_succ_of_lt hj,hl,hu⟩
      · rintro ⟨j,hj,hl,hu⟩
        have hj' : j < n := by
          by_contra hn
          have : j = n := by omega
          subst j
          omega
        exact ⟨j,hj',hl,hu⟩
    · rw [List.getElem?_append_right (by simpa [words_length] using Nat.le_of_not_gt h),
        words_length,get_word]
      constructor
      · intro hi; exact ⟨n,by omega,by omega,by omega⟩
      · rintro ⟨j,hj,hl,hu⟩
        have hjn : j = n := by
          by_contra hne
          have hj' : j+1 ≤ n := by omega
          have hp := offset_mono f hj'
          rw [offset_succ] at hp
          omega
        subst j
        omega

lemma indicator_exists (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    (∑ j ∈ range n, if p j then 1 else 0) ≠ 0 ↔ ∃ j < n, p j := by
  rw [← Nat.pos_iff_ne_zero,Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [Finset.mem_range]
  constructor
  · rintro ⟨j,hj,hv⟩
    exact ⟨j,hj,by by_contra hp; simp [hp] at hv⟩
  · rintro ⟨j,hj,hp⟩
    exact ⟨j,hj,by simp [hp]⟩

open scoped BigOperators
open Finset
open IndependentSetsCut.CounterMachine.Expr

def atIndex (v i : Expr) : Expr := v.subst (fun _ => i)
def closed (n : Expr) : Expr := atIndex n (.const 0)
def totalLength (n v : Expr) : Expr :=
  .sum (closed n) (.add (atIndex v (.arg 0)) (.const 1))
def startOffset (v : Expr) : Expr :=
  .sum (.arg 0) (.add (atIndex v (.arg 0)) (.const 1))
def wordBit (n v : Expr) : Expr :=
  .sum (closed n) (.mul (Expr.le (startOffset v) (.arg 1))
    (Expr.lt (.arg 1) (.add (startOffset v) (atIndex v (.arg 0)))))

@[simp] lemma atIndex_eval (v i : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (atIndex v i).eval s a = v.eval s (fun _ => i.eval s a) := by
  simp [atIndex]
@[simp] lemma closed_eval (n : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (closed n).eval s a = n.eval s (fun _ => 0) := by simp [closed,Expr.eval]
@[simp] lemma totalLength_eval (n v : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (totalLength n v).eval s a = offset (fun j => v.eval s (fun _ => j))
      (n.eval s (fun _ => 0)) := by
  simp [totalLength,Expr.eval,Expr.bind,offset]
@[simp] lemma startOffset_eval (v : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (startOffset v).eval s a = offset (fun j => v.eval s (fun _ => j)) (a 0) := by
  simp [startOffset,Expr.eval,Expr.bind,offset]
lemma wordBit_eval (n v : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (wordBit n v).eval s a = ∑ j ∈ range (n.eval s (fun _ => 0)),
      if offset (fun j => v.eval s (fun _ => j)) j ≤ a 0 ∧
        a 0 < offset (fun j => v.eval s (fun _ => j)) j + v.eval s (fun _ => j)
      then 1 else 0 := by
  simp only [wordBit,Expr.eval,closed_eval,Expr.le_eval,Expr.lt_eval,
    startOffset_eval,atIndex_eval,Expr.bind,Expr.indicator_and]

lemma table_eq_words (n v : Expr) (s : List Bool) :
    table (totalLength n v) (wordBit n v) s =
      words (fun j => v.eval s (fun _ => j)) (n.eval s (fun _ => 0)) := by
  apply List.ext_getElem
  · simp [table,words_length]
  · intro i hi hj
    simp only [table,List.getElem_ofFn]
    have hw := words_bit (fun j => v.eval s (fun _ => j)) (n.eval s (fun _ => 0)) i
    rw [List.getElem?_eq_getElem hj,Option.getD_some] at hw
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq,wordBit_eval,indicator_exists] using hw.symm

noncomputable def computer (n v : Expr) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) id
      (fun s => words (fun j => v.eval s (fun _ => j)) (n.eval s (fun _ => 0))) where
  tm := (tableComputer (totalLength n v) (wordBit n v)).tm
  inputAlphabet := (tableComputer (totalLength n v) (wordBit n v)).inputAlphabet
  outputAlphabet := (tableComputer (totalLength n v) (wordBit n v)).outputAlphabet
  time := (tableComputer (totalLength n v) (wordBit n v)).time
  outputsFun s := by
    simpa only [table_eq_words] using
      (tableComputer (totalLength n v) (wordBit n v)).outputsFun s

lemma computer_finiteAlphabet (n v : Expr) (k : (computer n v).tm.K) :
    Finite ((computer n v).tm.Γ k) := by
  exact tableComputer_finiteAlphabet (totalLength n v) (wordBit n v) k
end

noncomputable def encodedComputer {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) (n v : Expr)
    (spec : ∀ a, words (fun j => v.eval (ea a) (fun _ => j))
      (n.eval (ea a) (fun _ => 0)) = eb (f a)) :
    Turing.TM2ComputableInPolyTime ea eb f where
  tm := (computer n v).tm
  inputAlphabet := (computer n v).inputAlphabet
  outputAlphabet := (computer n v).outputAlphabet
  time := (computer n v).time
  outputsFun a := by simpa only [spec, id_eq] using (computer n v).outputsFun (ea a)

lemma encodedComputer_finiteAlphabet {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) (n v : Expr) (spec) (k : (encodedComputer ea eb f n v spec).tm.K) :
    Finite ((encodedComputer ea eb f n v spec).tm.Γ k) := computer_finiteAlphabet n v k
end IndependentSetsCut.CounterMachine.UnaryTables

end OAI
