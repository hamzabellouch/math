import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.FinalLabel

namespace OAI

namespace IndependentSetsCut.CounterMachine

section
open scoped BigOperators
variable {R : Type} [DecidableEq R]

omit [DecidableEq R] in
@[ext] theorem Data.ext {d e : Data R} (hr : d.reg = e.reg)
    (hi : d.input = e.input) (hb : d.backup = e.backup) (ho : d.output = e.output) : d = e := by
  cases d; cases e; simp_all

namespace Command

theorem Within.loop (r : R) (b : Command R) (state : ℕ → Data R) (n B : ℕ)
    (hr : ∀ i ≤ n, (state i).reg r = i)
    (hb : ∀ i < n, Within b (decData (state (i+1)) r) (state i) B) :
    Within (.loop r b) (state n) (state 0) (n * (B + 1) + 1) := by
  induction n with
  | zero => exact ⟨1, by omega, Evaluates.loop_zero (hr 0 le_rfl)⟩
  | succ n ih =>
    obtain ⟨a, ha, ea⟩ := hb n (by omega)
    obtain ⟨b', hb', eb⟩ := ih (fun i hi => hr i (by omega)) (fun i hi => hb i (by omega))
    refine ⟨1 + a + b', ?_, Evaluates.loop_pos (by rw [hr (n+1) le_rfl]; omega) ea eb⟩
    nlinarith

 theorem Within.inc (d : Data R) (r : R) : Within (.inc r) d (incData d r) 1 :=
  ⟨1, le_rfl, Evaluates.inc d r⟩
 theorem Within.dec (d : Data R) (r : R) : Within (.dec r) d (decData d r) 1 :=
  ⟨1, le_rfl, Evaluates.dec d r⟩
 theorem Within.skip (d : Data R) : Within (.skip : Command R) d d 1 :=
  ⟨1, le_rfl, Evaluates.skip d⟩
 theorem Within.clear (d : Data R) (r : R) :
    Within (clear r) d (d.set r 0) (2*d.reg r+1) :=
  ⟨_, le_rfl, clear_evaluates d r⟩
 theorem Within.move (d : Data R) (r s : R) (h : r ≠ s) :
    Within (move r s) d ((d.set r 0).set s (d.reg s+d.reg r)) (2*d.reg r+1) :=
  ⟨_, le_rfl, move_evaluates d r s h⟩

def copy (r s t : R) : Command R :=
  .seq (.loop r (.seq (.inc s) (.inc t))) (move t r)

 theorem copy_evaluates (d : Data R) (r s t : R)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (ht : d.reg t = 0) :
    Within (copy r s t) d (d.set s (d.reg s + d.reg r)) (5*d.reg r+2) := by
  let n := d.reg r
  let state : ℕ → Data R := fun i => ((d.set r i).set s (d.reg s+n-i)).set t (n-i)
  have hn : state n = d := by
    ext u <;> simp [state, Data.set, n]
    by_cases hu : u = r <;> by_cases hs : u = s <;> by_cases ht' : u = t <;> simp_all
  have hloop : Within (.loop r (.seq (.inc s) (.inc t))) (state n) (state 0) (n*3+1) := by
    apply Within.loop r _ state n 2
    · intro i hi; simp [state, Data.set, hrs, hrt]
    · intro i hi
      have he := (Within.inc (decData (state (i+1)) r) s).seq
        (Within.inc (incData (decData (state (i+1)) r) s) t)
      have hout : incData (incData (decData (state (i+1)) r) s) t = state i := by
        ext u <;> simp only [incData, decData, state, Data.set]
        by_cases hu : u = r <;> by_cases hs : u = s <;> by_cases ht' : u = t <;>
          simp [hu, hs, ht', hrs, hrt, hst, Ne.symm hrs, Ne.symm hrt, Ne.symm hst] <;> omega
      simpa only [hout] using he
  rw [hn] at hloop
  have hm := Within.move (state 0) t r (Ne.symm hrt)
  have hout : ((state 0).set t 0).set r ((state 0).reg r + (state 0).reg t) =
      d.set s (d.reg s + d.reg r) := by
    ext u <;> simp only [state, Data.set]
    by_cases hu : u = r <;> by_cases hs : u = s <;> by_cases ht' : u = t <;>
      simp [hu, hs, ht', hrs, hrt, hst, Ne.symm hrs, Ne.symm hrt, Ne.symm hst, ht, n]
  have ht' : (state 0).reg t = n := by simp [state, Data.set]
  have h := hloop.seq hm
  rw [hout, ht'] at h
  convert h using 1 <;> dsimp [copy, n] ; omega

def mulAdd (count source target backup : R) : Command R :=
  .loop count (copy source target backup)

 theorem mulAdd_evaluates (d : Data R) (c r s t : R)
    (hcr : c ≠ r) (hcs : c ≠ s) (hct : c ≠ t)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (ht : d.reg t = 0) :
    Within (mulAdd c r s t) d ((d.set c 0).set s (d.reg s+d.reg c*d.reg r))
      (d.reg c*(5*d.reg r+3)+1) := by
  let n := d.reg c
  let state : ℕ → Data R := fun i => (d.set c i).set s (d.reg s+(n-i)*d.reg r)
  have hn : state n = d := by
    simp [state, n]
  have hloop : Within (.loop c (copy r s t)) (state n) (state 0)
      (n*(5*d.reg r+3)+1) := by
    apply Within.loop c _ state n (5*d.reg r+2)
    · intro i hi; simp [state, Data.set, hcs]
    · intro i hi
      have hr' : (decData (state (i+1)) c).reg r = d.reg r := by
        simp [state, decData, Data.set, Ne.symm hcr, hrs]
      have ht' : (decData (state (i+1)) c).reg t = 0 := by
        simp [state, decData, Data.set, Ne.symm hct, Ne.symm hst, ht]
      have h := copy_evaluates (decData (state (i+1)) c) r s t hrs hrt hst ht'
      rw [hr'] at h
      have hout : (decData (state (i+1)) c).set s
          ((decData (state (i+1)) c).reg s + d.reg r) = state i := by
        have hh : (n-(i+1))*d.reg r+d.reg r = (n-i)*d.reg r := by
          have : n-i = n-(i+1)+1 := by omega
          rw [this, Nat.add_mul, Nat.one_mul]
        ext u <;> simp only [decData, state, Data.set]
        by_cases hu : u = c <;> by_cases hs : u = s <;>
          simp [hu, hs, hcs, Ne.symm hcs, Nat.add_assoc] ; omega
      simpa only [hout] using h
  simpa [mulAdd, hn, state, n] using hloop

end Command
end

variable {R : Type} [DecidableEq R]
namespace Command

def put (r : R) : ℕ → Command R
  | 0 => .skip
  | n+1 => .seq (.inc r) (put r n)

 theorem put_evaluates (d : Data R) (r : R) (n : ℕ) :
    Within (put r n) d (d.set r (d.reg r+n)) (n+1) := by
  induction n generalizing d with
  | zero => simpa [put] using Within.skip d
  | succ n ih =>
    have h := (Within.inc d r).seq (ih (incData d r))
    have he : (incData d r).set r ((incData d r).reg r+n) = d.set r (d.reg r+(n+1)) := by
      simp [incData, Data.set, Nat.add_assoc, Nat.add_comm]
    rw [he] at h
    simpa only [put, show 1+(n+1) = n+1+1 by omega] using h

 def subFrom (r s : R) : Command R := .loop r (.dec s)

 theorem subFrom_evaluates (d : Data R) (r s : R) (h : r ≠ s) :
    Within (subFrom r s) d ((d.set r 0).set s (d.reg s-d.reg r)) (2*d.reg r+1) := by
  let n := d.reg r
  let state : ℕ → Data R := fun i => (d.set r i).set s (d.reg s-(n-i))
  have hn : state n = d := by simp [state, n]
  have hl : Within (.loop r (.dec s)) (state n) (state 0) (n*2+1) := by
    apply Within.loop r _ state n 1
    · intro i hi; simp [state, Data.set, h]
    · intro i hi
      have he : decData (decData (state (i+1)) r) s = state i := by
        ext u <;> simp only [decData, state, Data.set]
        by_cases hu : u = r <;> by_cases hs : u = s <;>
          simp [hu, hs, h, Ne.symm h] ; omega
      simpa only [he] using Within.dec (decData (state (i+1)) r) s
  simpa [subFrom, state, n, hn, Nat.mul_comm] using hl

 theorem rewind_evaluates (d : Data R) :
    Within (.rewind : Command R) d {d with input := d.backup.reverse++d.input, backup := []}
      (d.backup.length+1) := by
  generalize he : d.backup = xs
  induction xs generalizing d with
  | nil =>
    have hd : {d with input := [].reverse++d.input, backup := []} = d := by
      cases d; simp_all
    exact ⟨1, by simp, by rw [hd]; exact Evaluates.rewind_empty he⟩
  | cons b rest ih =>
    have hb : (backData d).backup = rest := by simp [backData, he]
    obtain ⟨n, hn, h⟩ := ih (backData d) hb
    have hout : {backData d with input := rest.reverse++(backData d).input, backup := []} =
        {d with input := (b::rest).reverse++d.input, backup := []} := by
      simp [backData, he, List.reverse_cons, List.append_assoc]
    rw [hout] at h
    exact ⟨1+n, by simp; omega, Evaluates.rewind_cons he h⟩

def skipInput (r : R) : Command R := .loop r (.read .skip .skip .skip)

 theorem skipInput_evaluates (d : Data R) (r : R) :
    Within (skipInput r) d
      {(d.set r 0) with input := d.input.drop (d.reg r), backup := (d.input.take (d.reg r)).reverse++d.backup}
      (3*d.reg r+1) := by
  generalize hn : d.reg r = n
  induction n generalizing d with
  | zero =>
    have he : {d.set r 0 with input := d.input.drop 0, backup := (d.input.take 0).reverse++d.backup} = d := by
      simp only [List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append]
      rw [← hn, Data.set_self]
    rw [he]
    exact ⟨1, by omega, Evaluates.loop_zero hn⟩
  | succ n ih =>
    let e := readData (decData d r)
    have he : e.reg r = n := by simp [e, readData, decData, hn]
    obtain ⟨a, ha, hr⟩ := ih e he
    have hb : Evaluates (.read .skip .skip .skip) (decData d r) e 2 := by
      cases hinput : d.input with
      | nil => exact Evaluates.read_empty (d := decData d r) hinput (Evaluates.skip _)
      | cons b rest =>
        cases b
        · exact Evaluates.read_zero (d := decData d r) hinput (Evaluates.skip _)
        · exact Evaluates.read_one (d := decData d r) hinput (Evaluates.skip _)
    have hout : {e.set r 0 with input := e.input.drop n, backup := (e.input.take n).reverse++e.backup} =
        {d.set r 0 with input := d.input.drop (n+1), backup := (d.input.take (n+1)).reverse++d.backup} := by
      cases hi : d.input with
      | nil => simp [e, readData, decData, Data.set, hi]
      | cons b rest => simp [e, readData, decData, Data.set, hi, List.reverse_cons, List.append_assoc]
    rw [hout] at hr
    refine ⟨1+2+a, by omega, Evaluates.loop_pos (by omega) hb hr⟩

def inputBit (index result : R) : Command R :=
  .seq (skipInput index) (.seq (.read (.inc result) .skip .skip) .rewind)

 theorem inputBit_evaluates (d : Data R) (i r : R) (hir : i ≠ r)
    (hb : d.backup = []) (hr : d.reg r = 0) :
    Within (inputBit i r) d ((d.set i 0).set r (if d.input[d.reg i]?.getD false then 1 else 0))
      (3*d.reg i+d.input.length+4) := by
  let e : Data R := {d.set i 0 with input := d.input.drop (d.reg i), backup := (d.input.take (d.reg i)).reverse++d.backup}
  have he := skipInput_evaluates d i
  let bit := (d.input[d.reg i]?).getD false
  let f : Data R := (readData e).set r (if bit then 1 else 0)
  have hread : Within (.read (.inc r) .skip .skip) e f 2 := by
    have er : e.reg r = 0 := by simp [e, Data.set, Ne.symm hir, hr]
    have bit_head : (e.input.head?).getD false = bit := by
      simp [e, bit, List.head?_drop]
    cases hi : e.input with
    | nil =>
      have hbit : bit = false := by simpa [hi] using bit_head.symm
      have hf : f = readData e := by simp [f, hbit, readData, ← er]
      exact ⟨2, le_rfl, by rw [hf]; exact Evaluates.read_empty hi (Evaluates.skip _)⟩
    | cons b rest =>
      cases b
      · have hbit : bit = false := by simpa [hi] using bit_head.symm
        have hf : f = readData e := by simp [f, hbit, readData, ← er]
        exact ⟨2, le_rfl, by rw [hf]; exact Evaluates.read_zero hi (Evaluates.skip _)⟩
      · have hbit : bit = true := by simpa [hi] using bit_head.symm
        have hf : f = incData (readData e) r := by simp [f, hbit, incData, Data.set, readData, er]
        exact ⟨2, le_rfl, by rw [hf]; exact Evaluates.read_one hi (Evaluates.inc _ _)⟩
  have hrew := rewind_evaluates f
  have restored : {f with input := f.backup.reverse++f.input, backup := []} =
      (d.set i 0).set r (if bit then 1 else 0) := by
    have heq : e.backup.reverse ++ e.input = d.input := by
      simp [e, hb]
    have heq' : (readData e).backup.reverse ++ (readData e).input = d.input := by
      rw [readData]
      simp only [List.reverse_append, List.reverse_take]
      cases hi : e.input <;> simpa [hi, List.append_assoc] using heq
    apply Data.ext
    · rfl
    · exact heq'
    · exact hb.symm
    · rfl
  have size : f.backup.length ≤ d.input.length := by
    dsimp [f, Data.set, readData, e]
    simp only [List.length_append, List.length_take, List.length_reverse, hb, List.length_nil,
      add_zero, List.length_drop]
    omega
  have hh := he.seq (hread.seq hrew)
  rw [restored] at hh
  exact hh.mono (by omega)

end Command
end IndependentSetsCut.CounterMachine

end OAI
