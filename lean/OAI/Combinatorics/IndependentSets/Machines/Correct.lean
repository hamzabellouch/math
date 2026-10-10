import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.LengthLoop

namespace OAI

namespace IndependentSetsCut.CounterMachine.Expr
open scoped BigOperators
open Finset Command

def Correct (e : Expr) : Prop := ∀ (vars : ℕ → ℕ) (k : ℕ) (d : Data ℕ) (M : ℕ),
    (∀ i, vars i < k) → d.Clean k → d.backup = [] → d.input.length ≤ M →
    (∀ i, d.reg (vars i) ≤ M) →
    Within (e.compile vars k) d (d.set k (e.eval d.input (fun i => d.reg (vars i)))) (e.timeBudget M)

 theorem correct_const (n : ℕ) : Correct (.const n) := by
  intro vars k d M hv hc hb hi ha
  simpa [compile, eval, timeBudget, hc k le_rfl] using put_evaluates d k n

 theorem correct_arg (i : ℕ) : Correct (.arg i) := by
  intro vars k d M hv hc hb hi ha
  have he := copy_evaluates d (vars i) k (k+1) (by have := hv i; omega)
    (by have := hv i; omega) (by omega) (hc _ (by omega))
  simp only [hc k le_rfl, zero_add] at he
  exact he.mono (by dsimp [timeBudget]; have := ha i; omega)

 theorem correct_length : Correct .length := by
  intro vars k d M hv hc hb hi ha
  exact (inputLength_evaluates d (k+1) k (by omega) (hc _ (by omega)) (hc _ le_rfl) hb).mono
    (by dsimp [timeBudget]; omega)

 theorem binary_start {a b : Expr} (hca : Correct a) (hcb : Correct b)
    (vars : ℕ → ℕ) (k : ℕ) (d : Data ℕ) (M : ℕ)
    (hv : ∀ i, vars i < k) (hc : d.Clean k) (hb : d.backup = []) (hi : d.input.length ≤ M)
    (ha : ∀ i, d.reg (vars i) ≤ M) :
    Within (.seq (a.compile vars k) (b.compile vars (k+1))) d
      ((d.set k (a.eval d.input (fun i => d.reg (vars i)))).set (k+1)
        (b.eval d.input (fun i => d.reg (vars i))))
      (a.timeBudget M+b.timeBudget M) := by
  have h1 := hca vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  have h2 := hcb vars (k+1) (d.set k A) M (fun i => by have := hv i; omega)
    (hc.set_succ A) hb hi (fun i => by
      rw [Data.set_reg_ne d k (vars i) A (Nat.ne_of_lt (hv i))]
      exact ha i)
  rw [Data.set_args d vars k A hv] at h2
  exact h1.seq h2

 theorem correct_add {a b : Expr} (hca : Correct a) (hcb : Correct b) : Correct (.add a b) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := b.eval d.input (fun i => d.reg (vars i))
  let e := (d.set k A).set (k+1) B
  have hs := binary_start hca hcb vars k d M hv hc hb hi ha
  have hm := Within.move e (k+1) k (by omega)
  have hout : (e.set (k+1) 0).set k (e.reg k+e.reg (k+1)) = d.set k (A+B) := by
    have hz := hc (k+1) (by omega)
    apply Data.ext
    · ext u
      by_cases hu : u = k <;> by_cases hu' : u = k+1 <;>
        simp [e, Data.set, hu, hu', hz]
    all_goals rfl
  have hm' : Within (move (k+1) k) e (d.set k (A+B)) (2*B+1) := by
    rw [hout] at hm
    simpa only [show e.reg (k+1) = B by simp [e]] using hm
  obtain ⟨s, hsb, hse⟩ := hs
  cases hse with
  | seq h1 h2 =>
    have hh := (show Within _ _ _ _ from ⟨_,le_rfl,h1⟩).seq
      ((show Within _ _ _ _ from ⟨_,le_rfl,h2⟩).seq hm')
    exact hh.mono (by have hB := b.eval_le d.input _ M hi ha; dsimp [timeBudget, B] at *; omega)

 theorem correct_sub {a b : Expr} (hca : Correct a) (hcb : Correct b) : Correct (.sub a b) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := b.eval d.input (fun i => d.reg (vars i))
  let e := (d.set k A).set (k+1) B
  have hs := binary_start hca hcb vars k d M hv hc hb hi ha
  have hm := subFrom_evaluates e (k+1) k (by omega)
  have hout : (e.set (k+1) 0).set k (e.reg k-e.reg (k+1)) = d.set k (A-B) := by
    have hz := hc (k+1) (by omega)
    apply Data.ext
    · ext u
      by_cases hu : u = k <;> by_cases hu' : u = k+1 <;>
        simp [e, Data.set, hu, hu', hz]
    all_goals rfl
  have hm' : Within (subFrom (k+1) k) e (d.set k (A-B)) (2*B+1) := by
    rw [hout] at hm
    simpa only [show e.reg (k+1) = B by simp [e]] using hm
  obtain ⟨s, hsb, hse⟩ := hs
  cases hse with
  | seq h1 h2 =>
    have hh := (show Within _ _ _ _ from ⟨_,le_rfl,h1⟩).seq
      ((show Within _ _ _ _ from ⟨_,le_rfl,h2⟩).seq hm')
    exact hh.mono (by have hB := b.eval_le d.input _ M hi ha; dsimp [timeBudget, B] at *; omega)

 theorem correct_zero {a : Expr} (hca : Correct a) : Correct (.zero a) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  have h1 := hca vars k d M hv hc hb hi ha
  have h2 : Within (.test k (.inc k) (clear k)) (d.set k A)
      (d.set k (if A=0 then 1 else 0)) (2*A+2) := by
    by_cases hA : A=0
    · refine ⟨2, by omega, Evaluates.test_zero (r := k) (n := 1) (d := d.set k A) (by simp [hA]) ?_⟩
      simpa [hA, incData, Data.set] using Evaluates.inc (d.set k A) k
    · refine ⟨1+(2*A+1), by omega, Evaluates.test_pos (r := k) (d := d.set k A) (by simpa using hA) ?_⟩
      simpa [hA] using clear_evaluates (d.set k A) k
  have h := h1.seq h2
  exact h.mono (by dsimp [timeBudget]; have := a.eval_le d.input _ M hi ha; dsimp [A] at *; omega)

 theorem correct_bit {a : Expr} (hca : Correct a) : Correct (.bit a) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := if (d.input[A]?).getD false then 1 else 0
  have h1 := hca vars k d M hv hc hb hi ha
  have h2 := inputBit_evaluates (d.set k A) k (k+1) (by omega) hb
    (by rw [Data.set_reg_ne _ _ _ _ (by omega)]; exact hc _ (by omega))
  have hout2 : ((d.set k A).set k 0).set (k+1) B = d.set (k+1) B := by
    rw [Data.set_set, Data.set_clean_zero hc le_rfl]
  simp only [Data.set_reg_same] at h2
  change Within (inputBit k (k+1)) (d.set k A)
    (((d.set k A).set k 0).set (k+1) B) (3*A+d.input.length+4) at h2
  rw [hout2] at h2
  have h3 := Within.move (d.set (k+1) B) (k+1) k (by omega)
  have hout3 : ((d.set (k+1) B).set (k+1) 0).set k
      ((d.set (k+1) B).reg k+(d.set (k+1) B).reg (k+1)) = d.set k B := by
    simp only [Data.set_set]
    rw [Data.set_clean_zero hc (by omega)]
    simp [Data.set, hc k le_rfl]
  have h3' : Within (move (k+1) k) (d.set (k+1) B) (d.set k B) (2*B+1) := by
    rw [hout3] at h3
    simpa only [Data.set_reg_same] using h3
  have h := h1.seq (h2.seq h3')
  have hB : B ≤ 1 := by dsimp [B]; split_ifs <;> omega
  exact h.mono (by have hA := a.eval_le d.input _ M hi ha; dsimp [timeBudget, A] at *; omega)

end IndependentSetsCut.CounterMachine.Expr

namespace IndependentSetsCut.CounterMachine.Command
variable {R : Type} [DecidableEq R]
 theorem Within.assoc {a b c : Command R} {d e : Data R} {B : ℕ}
    (h : Within (.seq (.seq a b) c) d e B) : Within (.seq a (.seq b c)) d e B := by
  obtain ⟨n, hn, he⟩ := h
  cases he with
  | seq hab hc =>
    cases hab with
    | seq ha hb =>
      exact ⟨_, by omega, Evaluates.seq ha (Evaluates.seq hb hc)⟩
end IndependentSetsCut.CounterMachine.Command
namespace IndependentSetsCut.CounterMachine.Expr
open Command

 theorem correct_mul {a b : Expr} (hca : Correct a) (hcb : Correct b) : Correct (.mul a b) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := b.eval d.input (fun i => d.reg (vars i))
  let e := (d.set k A).set (k+1) B
  have hs := binary_start hca hcb vars k d M hv hc hb hi ha
  have hz1 := hc (k+1) (by omega)
  have hz2 := hc (k+2) (by omega)
  have hz3 := hc (k+3) (by omega)
  have hm := mulAdd_evaluates e (k+1) k (k+2) (k+3) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by simp [e, hz3, Data.set])
  have hout : (e.set (k+1) 0).set (k+2) (e.reg (k+2)+e.reg (k+1)*e.reg k) =
      (d.set k A).set (k+2) (A*B) := by
    apply Data.ext
    · ext u
      by_cases h0 : u = k <;> by_cases h1 : u = k+1 <;> by_cases h2 : u = k+2 <;>
        simp [e, Data.set, h0, h1, h2, hz1, hz2, Nat.mul_comm]
    all_goals rfl
  rw [hout] at hm
  have hm' : Within (mulAdd (k+1) k (k+2) (k+3)) e ((d.set k A).set (k+2) (A*B))
      (B*(5*A+3)+1) := by simpa [e, Data.set] using hm
  let f := (d.set k A).set (k+2) (A*B)
  have hf := Within.clear f k
  have houtf : f.set k 0 = d.set (k+2) (A*B) := by
    change (((d.set k A).set (k+2) (A*B)).set k 0) = _
    rw [Data.set_comm _ k (k+2) _ _ (by omega)]
    rw [Data.set_set]
    rw [Data.set_comm _ (k+2) k _ _ (by omega), Data.set_clean_zero hc le_rfl]
  rw [houtf] at hf
  have hf' : Within (clear k) f (d.set (k+2) (A*B)) (2*A+1) := by
    simpa [f, Data.set] using hf
  have hg := Within.move (d.set (k+2) (A*B)) (k+2) k (by omega)
  have houtg : ((d.set (k+2) (A*B)).set (k+2) 0).set k
      ((d.set (k+2) (A*B)).reg k+(d.set (k+2) (A*B)).reg (k+2)) = d.set k (A*B) := by
    rw [Data.set_set, Data.set_clean_zero hc (by omega)]
    simp [Data.set, hc k le_rfl]
  rw [houtg] at hg
  have hg' : Within (move (k+2) k) (d.set (k+2) (A*B)) (d.set k (A*B)) (2*(A*B)+1) := by
    simpa only [Data.set_reg_same] using hg
  have hh := (hs.seq (hm'.seq (hf'.seq hg'))).assoc
  apply hh.mono
  have hA := a.eval_le d.input _ M hi ha
  have hB := b.eval_le d.input _ M hi ha
  change a.timeBudget M+b.timeBudget M+(B*(5*A+3)+1+(2*A+1+(2*(A*B)+1))) ≤ _
  change A ≤ a.valueBudget M at hA
  change B ≤ b.valueBudget M at hB
  dsimp only [timeBudget]
  calc
    _ ≤ a.timeBudget M+b.timeBudget M+
        (b.valueBudget M*(5*a.valueBudget M+3)+1+
          (2*a.valueBudget M+1+(2*(a.valueBudget M*b.valueBudget M)+1))) := by gcongr
    _ = _ := by omega

end IndependentSetsCut.CounterMachine.Expr

end OAI
