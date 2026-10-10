import Mathlib
import OAI.Probability.CriticalPercolation.Modular.WeightedCauchy
import OAI.Probability.CriticalPercolation.ProductMeasure.QueryMartingale

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_abs_sq_le (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0≤w e b) (f : (E → Prop) → ℝ) :
    (expect w (fun ω => |f ω|))^2 ≤ expect w (fun ω => (f ω)^2) := by
  have h := FiniteEntropy.weighted_cauchy (density w) (fun ω => |f ω|) (fun _ => 1)
    (fun ω => density_nonneg hn ω)
  simp only [mul_one,one_pow,sq_abs] at h
  have hw1 : ∑ ω, density w ω = 1 := by
    simpa only [expect,mul_one] using expect_const w hw (1:ℝ)
  simpa only [hw1,mul_one,expect] using h

lemma expect_abs_le_of_second_le (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0≤w e b) (f : (E → Prop) → ℝ) {a : ℝ} (ha : 0≤a)
    (hf : expect w (fun ω => (f ω)^2) ≤ a^2) : expect w (fun ω => |f ω|) ≤ a := by
  nlinarith [expect_abs_sq_le w hw hn f]

end CriticalPercolation.FiniteProduct
namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*}

lemma queryCount_eq_reads_length (t : SearchTree E R) (ω : E → Prop) :
    t.queryCount ω = (t.reads (fun e => decide (ω e))).length := by
  induction t with
  | done r => rfl
  | ask e l r hl hr =>
    by_cases he : ω e <;> simp [queryCount,reads,he,hl,hr,Nat.add_comm]

lemma centeredSum_eq_zero_of_count (t : SearchTree E R) (ω : E → Prop)
    (h : t.queryCount ω = 0) (p : ℝ) : t.centeredSum p ω = 0 := by
  cases t with
  | done r => rfl
  | ask e l r => simp [queryCount] at h

variable [Fintype E] [DecidableEq E]

lemma queryCount_le_card (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (ω : E → Prop) : t.queryCount ω ≤ Fintype.card E := by
  rw [queryCount_eq_reads_length]
  exact List.Nodup.length_le_card (t.reads_nodup used ht _)

lemma band_centered_bound (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (k : ℕ) :
    expect w (fun ω => if 4^k ≤ t.queryCount ω ∧ t.queryCount ω < 4^(k+1)
      then |t.centeredSum p ω| else 0) ≤ (2:ℝ)^(k+1) := by
  calc
    _ ≤ expect w (fun ω => |(t.truncate (4^(k+1))).centeredSum p ω|) := by
      apply expect_mono hn
      intro ω
      split_ifs with h
      · rw [t.centeredSum_truncate_eq _ ω h.2.le p]
      · exact abs_nonneg _
    _ ≤ (2:ℝ)^(k+1) := by
      apply expect_abs_le_of_second_le w hw hn _ (by positivity)
      have ht' := t.truncated_second_le used ht p hp w hw hn hf (4^(k+1))
      have hpp : p*(1-p) ≤ 1 := by nlinarith [hp.2,sq_nonneg p]
      have hN : (4^(k+1) : ℝ) = ((2:ℝ)^(k+1))^2 := by
        rw [← pow_mul, mul_comm (k+1) 2, pow_mul]
        norm_num
      calc _ ≤ p*(1-p)*(4^(k+1) : ℕ) := ht'
           _ ≤ (4^(k+1) : ℝ) := by
             simpa using mul_le_mul_of_nonneg_right hpp (by positivity : 0≤(4^(k+1):ℝ))
           _ = _ := hN

end CriticalPercolation.SearchTree
end
end
end

end OAI
