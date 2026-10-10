import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.PreparedShortRow

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

def rows : (n : ℕ) → Table Ω n → Finset Ω
  | 0, _ => ∅
  | n+1, z => insert z.1 (rows n z.2)

omit [Fintype Ω] in
lemma rows_card_le (n : ℕ) (z : Table Ω n) : (rows n z).card≤n := by
  induction n with
  | zero => simp [rows]
  | succ n ih => exact (card_insert_le _ _).trans (Nat.add_le_add_right (ih _) 1)

omit [Fintype Ω] in
lemma first_none_iff (A : Ω→Prop) (n : ℕ) (z : Table Ω n) :
    first A n z=none ↔ ∀ x∈rows n z,¬A x := by
  induction n with
  | zero => simp [first,rows]
  | succ n ih =>
    by_cases h : A z.1
    · simp [first,rows,h]
    · simpa [first,rows,h] using ih z.2

lemma missed_probability (p : Law Ω) (A : Ω→Prop) (n : ℕ) :
    (∑ z,tableWeight p n z*(if first A n z=none then 1 else 0))=(1-acceptProb p A)^n := by
  have hh (z : Table Ω n) :
      (if first A n z=none then (1:ℝ) else 0)=1-outcome A (fun _ => 1) n z := by
    unfold outcome
    cases first A n z <;> simp
  simp_rw [hh,mul_sub,mul_one]
  rw [sum_sub_distrib,tableWeight_total]
  change 1-integral p A (fun _ => 1) n=_
  rw [production_probability]
  ring

lemma missing_exp (p : Law Ω) (A : Ω→Prop) (n : ℕ) :
    (1-acceptProb p A)^n≤exp (-(n:ℝ)*acceptProb p A) := by
  have hh : 1-acceptProb p A≤exp (-acceptProb p A) := by
    have := add_one_le_exp (-acceptProb p A)
    linarith
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr (acceptProb_le_one p A)) hh n
  rw [←exp_nat_mul] at hp
  simpa only [mul_neg,neg_mul] using hp

theorem exists_universal (p : Law Ω) (A : ι→Ω→Prop) (n : ℕ)
    (h : (∑ i,(1-acceptProb p (A i))^n)<1) :
    ∃ z : Table Ω n,∀ i,∃ x∈rows n z,A i x := by
  by_contra! hn
  have hl (z : Table Ω n) :
      (1:ℝ)≤∑ i,if first (A i) n z=none then 1 else 0 := by
    obtain ⟨i,hi⟩ := hn z
    have hm : first (A i) n z=none := (first_none_iff _ _ _).mpr hi
    have hh := single_le_sum (f := fun i => if first (A i) n z=none then (1:ℝ) else 0)
      (fun i _ => by split_ifs <;> norm_num) (mem_univ i)
    simpa [hm] using hh
  have hh : (1:ℝ)≤∑ z,tableWeight p n z*(∑ i,if first (A i) n z=none then 1 else 0) := by
    calc
      _ = ∑ z,tableWeight p n z := (tableWeight_total p n).symm
      _ ≤ _ := by
        apply sum_le_sum
        intro z _
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hl z) (tableWeight_nonneg p n z)
  simp_rw [mul_sum] at hh
  rw [sum_comm] at hh
  simp_rw [missed_probability] at hh
  linarith

theorem exists_cover (p : Law Ω) (A : ι→Ω→Prop) (a H : ℝ)
    (ha : 0≤a) (hcard : (Fintype.card ι:ℝ)≤exp H) (hH : H+1≤exp a)
    (hp : ∀ i,exp (-a)≤acceptProb p (A i)) :
    ∃ r : Finset Ω,r.card≤⌈exp (2*a)⌉₊ ∧ (∀ i,∃ x∈r,A i x) ∧
      log ((⌈exp (2*a)⌉₊:ℝ)+1)≤2*a+log 3 := by
  let n := ⌈exp (2*a)⌉₊
  have hN : exp (2*a)≤(n:ℝ) := Nat.le_ceil _
  have hl : (∑ i,(1-acceptProb p (A i))^n)<1 := by
    calc
      _ ≤ (∑ _i : ι,exp (-(n:ℝ)*exp (-a))) := by
        apply sum_le_sum
        intro i _
        apply (missing_exp p (A i) n).trans
        apply exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (hp i) (Nat.cast_nonneg n : (0:ℝ)≤n)
        nlinarith only [hh]
      _ = (Fintype.card ι:ℝ)*exp (-(n:ℝ)*exp (-a)) := by simp
      _ ≤ exp H*exp (-(n:ℝ)*exp (-a)) := by gcongr
      _ = exp (H-(n:ℝ)*exp (-a)) := by rw [←exp_add]; congr 1; ring
      _ ≤ exp (-1) := by
        apply exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hN (exp_pos (-a)).le
        have he : exp (2*a)*exp (-a)=exp a := by rw [←exp_add]; congr 1; ring
        rw [he] at hh
        linarith
      _ < 1 := exp_lt_one_iff.mpr (by norm_num)
  obtain ⟨z,hz⟩ := exists_universal p A n hl
  refine ⟨rows n z,rows_card_le n z,hz,?_⟩
  have hn : (n:ℝ)<exp (2*a)+1 := Nat.ceil_lt_add_one (exp_pos _).le
  have he : 1≤exp (2*a) := one_le_exp_iff.mpr (by linarith)
  have hnp : (0:ℝ)<(n:ℝ)+1 := by positivity
  calc
    _ ≤ log (3*exp (2*a)) := by apply log_le_log hnp; linarith
    _ = _ := by rw [log_mul (by norm_num) (exp_ne_zero _),log_exp]; ring

end
end SharpLogRamsey.PublicTables

end

end OAI
