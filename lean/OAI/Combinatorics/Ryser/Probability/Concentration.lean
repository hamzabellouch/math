import OAI.Combinatorics.Ryser.Probability.Exposure
import OAI.Combinatorics.Ryser.Probability.Exponential

namespace OAI

namespace RyserCoveringCounterexample.Concentration

open scoped BigOperators
open Exposure

variable {Omega : Type*} [Fintype Omega]

theorem exposure_mgf (M : ℝ) (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (v : Fin n → ℝ) (theta : ℝ)
    (hb : ExposureBounds M n mu f v) (htheta : |theta| * M ≤ 1) :
    (FiniteLaw.pi mu).expectation
      (fun w => Real.exp (theta * (f w - (FiniteLaw.pi mu).expectation f)))
      ≤ Real.exp (theta ^ 2 * ∑ i, v i) := by
  classical
  induction n with
  | zero =>
    have hf : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext w
      apply congrArg f
      funext i
      exact Fin.elim0 i
    rw [hf]
    simp [FiniteLaw.expectation_const]
  | succ n ih =>
    rcases hb with ⟨hbound, hsecond, hrec⟩
    have hzero : (mu 0).expectation
        (fun x => headMean mu f x - (mu 0).expectation (headMean mu f)) = 0 := by
      rw [FiniteLaw.expectation_sub, FiniteLaw.expectation_const, sub_self]
    have hhead := FiniteLaw.expectation_exp_le_of_mean_zero (mu 0)
      (fun x => headMean mu f x - (mu 0).expectation (headMean mu f))
      M (v 0) theta hzero hbound hsecond htheta
    have htail (x : Omega) :
        (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
          (fun w => Real.exp (theta * (f (Fin.cons x w) - headMean mu f x)))
          ≤ Real.exp (theta ^ 2 * ∑ i : Fin n, v i.succ) := by
      exact ih (fun i => mu i.succ) (fun w => f (Fin.cons x w))
        (fun i => v i.succ) (hrec x)
    calc
      _ = (mu 0).expectation (fun x =>
          (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
            (fun w => Real.exp (theta *
              (f (Fin.cons x w) - (FiniteLaw.pi mu).expectation f)))) :=
        expectation_pi_succ (n := n) mu
          (fun w : Fin (n + 1) → Omega =>
            Real.exp (theta * (f w - (FiniteLaw.pi mu).expectation f)))
      _ = (mu 0).expectation (fun x =>
          (FiniteLaw.pi (fun i : Fin n => mu i.succ)).expectation
            (fun w => Real.exp (theta *
              (f (Fin.cons x w) - (mu 0).expectation (headMean mu f))))) := by
        rw [expectation_pi_succ mu f]
      _ ≤ Real.exp (theta ^ 2 * (v 0 + ∑ i : Fin n, v i.succ)) :=
        FiniteLaw.iterated_centered_mgf_le (mu 0)
          (fun _ => FiniteLaw.pi (fun i : Fin n => mu i.succ))
          (fun x w => f (Fin.cons x w)) (headMean mu f)
          ((mu 0).expectation (headMean mu f)) theta (v 0)
          (∑ i : Fin n, v i.succ) hhead htail
      _ = _ := by rw [Fin.sum_univ_succ]

theorem concentration (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (v : Fin n → ℝ) (M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hb : ExposureBounds M n mu f v) (hv : (∑ i, v i) ≤ V) :
    (FiniteLaw.pi mu).prob
        (fun w => u ≤ |f w - (FiniteLaw.pi mu).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  apply FiniteLaw.bernstein_abs_tail_of_mgf (FiniteLaw.pi mu)
    (fun w => f w - (FiniteLaw.pi mu).expectation f) M V u hM hV hu
  intro theta htheta
  exact (exposure_mgf M n mu f v theta hb htheta).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv (sq_nonneg theta)))

theorem coordinate_concentration (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (c : Fin n → ℝ) (M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hcoord : ∀ i w x, |f (Function.update w i x) - f w| ≤ c i)
    (hcM : ∀ i, c i ≤ M) (hcV : (∑ i, (c i) ^ 2) ≤ V) :
    (FiniteLaw.pi mu).prob
        (fun w => u ≤ |f w - (FiniteLaw.pi mu).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  exact concentration n mu f (fun i => (c i) ^ 2) M V u hM hV hu
    (exposureBounds_of_coordinateBound M n mu f c hcoord hcM) hcV

theorem rare_anchor_concentration (n : Nat)
    (mu : Fin n → FiniteLaw Omega) (f : (Fin n → Omega) → ℝ)
    (e : Omega) (C r : Fin n → ℝ) (rare : Fin n → Omega → Prop)
    (M V u : ℝ) (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hanchor : ∀ i w, |f w - f (Function.update w i e)| ≤ C i)
    (houtside : ∀ i w, ¬ rare i (w i) → f w = f (Function.update w i e))
    (hrare : ∀ i, (mu i).prob (rare i) ≤ r i)
    (hCM : ∀ i, 2 * C i ≤ M)
    (hCV : (∑ i, (C i) ^ 2 * r i) ≤ V) :
    (FiniteLaw.pi mu).prob
        (fun w => u ≤ |f w - (FiniteLaw.pi mu).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  exact concentration n mu f (fun i => (C i) ^ 2 * r i) M V u hM hV hu
    (exposureBounds_of_rareAnchor M n mu f e C r rare hanchor houtside hrare hCM)
    hCV

end RyserCoveringCounterexample.Concentration

end OAI
