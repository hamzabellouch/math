import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.QueryBand
import OAI.Probability.CriticalPercolation.Exploration.Score
import OAI.Probability.CriticalPercolation.Criticality.DyadicBound

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E] [DecidableEq E]

lemma normalized_centered_bound (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (K : ℕ) :
    expect w (fun ω => |t.centeredSum p ω| *
      min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) ≤ 6/(2:ℝ)^K := by
  let N := Fintype.card E + 1
  let a (k : ℕ) := min (1/(4:ℝ)^K) (1/(4:ℝ)^k)
  let b (k : ℕ) (ω : E → Prop) :=
    if 4^k ≤ t.queryCount ω ∧ t.queryCount ω < 4^(k+1)
      then |t.centeredSum p ω| else 0
  have ha (k : ℕ) : 0≤a k := by dsimp [a]; positivity
  have hb (k : ℕ) (ω : E → Prop) : 0≤b k ω := by
    dsimp [b]; split_ifs <;> positivity
  have hpoint (ω : E → Prop) : |t.centeredSum p ω| *
      min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ)) ≤
        ∑ k ∈ Finset.range N, b k ω * a k := by
    by_cases hT : t.queryCount ω = 0
    · rw [t.centeredSum_eq_zero_of_count ω hT p,abs_zero,zero_mul]
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (hb k ω) (ha k))
    · let k := Nat.log 4 (t.queryCount ω)
      have hklo : 4^k ≤ t.queryCount ω := Nat.pow_log_le_self 4 hT
      have hkhi : t.queryCount ω < 4^(k+1) := Nat.lt_pow_succ_log_self (by omega) _
      have hkN : k ∈ Finset.range N := by
        apply Finset.mem_range.mpr
        have h1 := Nat.log_le_self 4 (t.queryCount ω)
        have h2 := t.queryCount_le_card used ht ω
        dsimp [k,N]
        omega
      calc
        _ ≤ b k ω * a k := by
          have hband : 4^k ≤ t.queryCount ω ∧ t.queryCount ω < 4^(k+1) := ⟨hklo,hkhi⟩
          simp only [b,ite_eq_left hband]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply min_le_min le_rfl
          apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<(4:ℝ)^k)
          exact_mod_cast hklo
        _ ≤ _ := Finset.single_le_sum (fun j _ => mul_nonneg (hb j ω) (ha j)) hkN
  calc
    _ ≤ expect w (fun ω => ∑ k ∈ Finset.range N, b k ω * a k) := expect_mono hn hpoint
    _ = ∑ k ∈ Finset.range N, expect w (b k) * a k := by
      simp only [expect,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ ≤ ∑ k ∈ Finset.range N, (2:ℝ)^(k+1)*a k := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (t.band_centered_bound used ht p hp w hw hn hf k) (ha k)
    _ = ∑ k ∈ Finset.range N,
        min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k) := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp [a]
      rw [mul_min_of_nonneg _ _ (by positivity)]
      simp only [mul_one_div]
    _ ≤ _ := dyadic_sum_bound N K

end CriticalPercolation.SearchTree
end
end
end

end OAI
