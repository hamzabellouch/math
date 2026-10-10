import OAI.Analysis.CircleDomains.Modulus.LinePayment

namespace OAI

/-!
# Variation payment across finitely many gaps

The domain intervals of a line crossing a finite circle domain contribute
their actual derivative variation. Each intervening hole contributes only
the difference of the two endpoint traces. This is the finite telescoping
step in the manuscript's parallel-line payment estimate.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

theorem abs_sub_le_sum_segments_and_jumps (n : ℕ) (left right : Fin (n + 1) → ℝ) :
    |right (Fin.last n) - left 0| ≤
      (∑ i, |right i - left i|) +
        ∑ i : Fin n, |left i.succ - right i.castSucc| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprior := ih (fun i => left i.castSucc) (fun i => right i.castSucc)
    have htriangle : |right (Fin.last (n + 1)) - left 0| ≤
        |right (Fin.last (n + 1)) - left (Fin.last (n + 1))| +
        |left (Fin.last (n + 1)) - right (Fin.last n).castSucc| +
        |right (Fin.last n).castSucc - left 0| := by
      have heq : right (Fin.last (n + 1)) - left 0 =
          (right (Fin.last (n + 1)) - left (Fin.last (n + 1))) +
          (left (Fin.last (n + 1)) - right (Fin.last n).castSucc) +
          (right (Fin.last n).castSucc - left 0) := by ring
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    calc
      _ ≤ |right (Fin.last (n + 1)) - left (Fin.last (n + 1))| +
          |left (Fin.last (n + 1)) - right (Fin.last n).castSucc| +
          ((∑ i : Fin (n + 1), |right i.castSucc - left i.castSucc|) +
            ∑ i : Fin n, |left i.succ.castSucc - right i.castSucc.castSucc|) :=
        htriangle.trans (add_le_add le_rfl (by simpa only [Fin.castSucc_zero] using hprior))
      _ = _ := by
        rw [Fin.sum_univ_castSucc (fun i : Fin (n + 2) => |right i - left i|),
          Fin.sum_univ_castSucc (fun i : Fin (n + 1) => |left i.succ - right i.castSucc|)]
        simp only [Fin.castSucc_succ, Fin.succ_last]
        ring

theorem variation_le_integral_abs_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) :
    |f b - f a| ≤ ∫ x in a..b, |deriv f x| := by
  rw [← hf.integral_deriv_eq_sub]
  simpa only [Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_integral_norm (f := deriv f) hab)

theorem line_payment_across_finite_gaps
    (n : ℕ) (a b : Fin (n + 1) → ℝ) (f : Fin (n + 1) → ℝ → ℝ)
    (A : Fin n → ℝ) (hab : ∀ i, a i ≤ b i)
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) (a i) (b i))
    (hzero : f 0 (a 0) = 0) (hone : f (Fin.last n) (b (Fin.last n)) = 1)
    (hjumps : ∀ i : Fin n,
      |f i.succ (a i.succ) - f i.castSucc (b i.castSucc)| ≤ A i) :
    1 ≤ (∑ i, ∫ x in a i..b i, |deriv (f i) x|) + ∑ i, A i := by
  have hchain := abs_sub_le_sum_segments_and_jumps n
    (fun i => f i (a i)) (fun i => f i (b i))
  rw [hone, hzero] at hchain
  norm_num only [sub_zero, abs_one] at hchain
  exact hchain.trans (add_le_add
    (Finset.sum_le_sum (fun i _ => variation_le_integral_abs_deriv (hab i) (hf i)))
    (Finset.sum_le_sum (fun i _ => hjumps i)))

end CircleDomainRigidity

end OAI
