import Mathlib.Analysis.SpecialFunctions.Log.Base
import OAI.NumberTheory.Ostmann.QuadraticSieve
import OAI.NumberTheory.Ostmann.QuadraticSievePoissonWindows

namespace OAI

namespace Ostmann.QuadraticSieve

def squarefreeDyadicBase (v : ℕ) : ℕ := 2^(Nat.log 2 v)

noncomputable def binarySquarefreeRows (K j : ℕ) : Finset ℕ :=
  (oddSquarefreeUpTo K).filter (fun v => 2^j ≤ v ∧ v < 2^(j+1))

theorem squarefreeDyadicBase_bounds {v : ℕ} (hv : 0 < v) :
    0 < squarefreeDyadicBase v ∧ squarefreeDyadicBase v ≤ v ∧ v < 2*squarefreeDyadicBase v := by
  refine ⟨by unfold squarefreeDyadicBase; positivity,Nat.pow_log_le_self 2 hv.ne',?_⟩
  simpa only [squarefreeDyadicBase,pow_succ,mul_comm] using
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) v

theorem mem_binarySquarefreeRows {K j v : ℕ} :
    v ∈ binarySquarefreeRows K j ↔ v ∈ oddSquarefreeUpTo K ∧ Nat.log 2 v = j := by
  simp only [binarySquarefreeRows,Finset.mem_filter]
  constructor
  · rintro ⟨hv,hlo,hhi⟩
    exact ⟨hv,Nat.log_eq_of_pow_le_of_lt_pow hlo hhi⟩
  · rintro ⟨hv,hj⟩
    rw [←hj]
    exact ⟨hv,Nat.pow_log_le_self 2 (show v ≠ 0 by have h := (mem_oddSquarefreeUpTo.mp hv).1; omega),
      Nat.lt_pow_succ_log_self (by decide) v⟩

theorem sum_oddSquarefree_eq_dyadic {E : Type*} [AddCommMonoid E] (K : ℕ) (f : ℕ → E) :
    (∑ v ∈ oddSquarefreeUpTo K, f v) =
      ∑ j ∈ Finset.range (Nat.log 2 K+1), ∑ v ∈ binarySquarefreeRows K j, f v := by
  have hmaps (v : ℕ) (hv : v ∈ oddSquarefreeUpTo K) : Nat.log 2 v ∈ Finset.range (Nat.log 2 K+1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_oddSquarefreeUpTo.mp hv).2.1))
  rw [←Finset.sum_fiberwise_of_maps_to hmaps f]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ext v
  simp only [Finset.mem_filter,mem_binarySquarefreeRows]

theorem squarefreeDyadicBase_eq_of_mem {K j v : ℕ} (hv : v ∈ binarySquarefreeRows K j) :
    squarefreeDyadicBase v = 2^j := by
  unfold squarefreeDyadicBase
  rw [(mem_binarySquarefreeRows.mp hv).2]

theorem squarefree_dyadic_depth_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 0 < K →
      (Nat.log 2 K+1 : ℕ) ≤ C*(K : ℝ)^ε := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1+1/(ε*Real.log 2),by positivity,?_⟩
  intro K hK
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hlog := Real.natLog_le_logb K 2
  rw [Real.logb] at hlog
  have hgrowth := Real.log_le_rpow_div hKr.le hε
  have hone : 1 ≤ (K : ℝ)^ε := Real.one_le_rpow (by exact_mod_cast hK) hε.le
  have hdepth : (Nat.log 2 K : ℝ)*Real.log 2 ≤ Real.log (K : ℝ) :=
    (le_div_iff₀ hl).mp hlog
  have heq : (1+1/(ε*Real.log 2))*(K : ℝ)^ε*Real.log 2 =
      (K : ℝ)^ε*Real.log 2+(K : ℝ)^ε/ε := by field_simp
  apply (mul_le_mul_iff_left₀ hl).mp
  rw [heq]
  push_cast
  nlinarith

end Ostmann.QuadraticSieve

end OAI
