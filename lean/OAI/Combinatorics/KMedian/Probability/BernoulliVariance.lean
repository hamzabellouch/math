import Mathlib
import OAI.Combinatorics.KMedian.Probability.BernoulliBatches
import OAI.Combinatorics.KMedian.Probability.FiniteVariance

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw

private def bitsConsEquiv (n : ℕ) : Bool × (Fin n → Bool) ≃ (Fin (n+1) → Bool) where
  toFun z := Fin.cons z.1 z.2
  invFun ω := (ω 0, Fin.tail ω)
  left_inv z := by cases z; simp
  right_inv ω := Fin.cons_self_tail ω

theorem bernoulli_expect_succ {n : ℕ} (p : Fin (n+1) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (f : (Fin (n+1) → Bool) → ℝ) :
    (bernoulli p hp0 hp1).expect f =
      (1-p 0)*(bernoulli (fun i => p i.succ) (fun i => hp0 i.succ) (fun i => hp1 i.succ)).expect
        (fun ω => f (Fin.cons false ω))+
      p 0*(bernoulli (fun i => p i.succ) (fun i => hp0 i.succ) (fun i => hp1 i.succ)).expect
        (fun ω => f (Fin.cons true ω)) := by
  unfold expect bernoulli
  rw [← (bitsConsEquiv n).sum_comp]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [bitsConsEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, coinWeight_true, coinWeight_false, mul_assoc, Finset.mul_sum]
  ring

theorem bernoulli_variance_succ {n : ℕ} (p : Fin (n+1) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (f : (Fin (n+1) → Bool) → ℝ) :
    let μ := bernoulli (fun i : Fin n => p i.succ) (fun i => hp0 i.succ) (fun i => hp1 i.succ)
    (bernoulli p hp0 hp1).variance f =
      (1-p 0)*μ.variance (fun ω => f (Fin.cons false ω))+
      p 0*μ.variance (fun ω => f (Fin.cons true ω))+
      p 0*(1-p 0)*(μ.expect (fun ω => f (Fin.cons true ω))-
        μ.expect (fun ω => f (Fin.cons false ω)))^2 := by
  dsimp only
  simp only [variance_eq, bernoulli_expect_succ]
  ring

theorem bernoulli_variance_bounded_differences : ∀ n : ℕ,
    ∀ (p C : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
      (_hC : ∀ i, 0 ≤ C i) (f : (Fin n → Bool) → ℝ),
    (∀ i ω, |f (Function.update ω i true)-f (Function.update ω i false)| ≤ C i) →
    (bernoulli p hp0 hp1).variance f ≤ ∑ i, p i*(1-p i)*(C i)^2 := by
  intro n
  induction n with
  | zero =>
    intro p C hp0 hp1 _ f _
    have hf : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext ω
      congr 1
      exact Subsingleton.elim _ _
    rw [hf, variance_const]
    simp
  | succ n ih =>
    intro p C hp0 hp1 hC f hdiff
    let μ := bernoulli (fun i : Fin n => p i.succ) (fun i => hp0 i.succ) (fun i => hp1 i.succ)
    let tailBound := ∑ i : Fin n, p i.succ*(1-p i.succ)*(C i.succ)^2
    have hb : ∀ b : Bool, μ.variance (fun ω => f (Fin.cons b ω)) ≤ tailBound := by
      intro b
      apply ih (fun i => p i.succ) (fun i => C i.succ)
        (fun i => hp0 i.succ) (fun i => hp1 i.succ) (fun i => hC i.succ)
        (fun ω => f (Fin.cons b ω))
      intro i ω
      simpa only [Fin.cons_update] using hdiff i.succ (Fin.cons b ω)
    have hm : |μ.expect (fun ω => f (Fin.cons true ω))-
        μ.expect (fun ω => f (Fin.cons false ω))| ≤ C 0 := by
      rw [← μ.expect_sub]
      calc
        _ ≤ μ.expect (fun ω => |f (Fin.cons true ω)-f (Fin.cons false ω)|) := μ.expect_abs_le _
        _ ≤ μ.expect (fun _ => C 0) := μ.expect_mono (fun ω => by
          simpa only [Fin.update_cons_zero] using hdiff 0 (Fin.cons false ω))
        _ = C 0 := μ.expect_const _
    have hmsq : (μ.expect (fun ω => f (Fin.cons true ω))-
        μ.expect (fun ω => f (Fin.cons false ω)))^2 ≤ (C 0)^2 :=
      by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (hC 0)).mpr hm
    rw [bernoulli_variance_succ, Fin.sum_univ_succ]
    change (1-p 0)*μ.variance (fun ω => f (Fin.cons false ω))+
      p 0*μ.variance (fun ω => f (Fin.cons true ω))+
      p 0*(1-p 0)*(μ.expect (fun ω => f (Fin.cons true ω))-
        μ.expect (fun ω => f (Fin.cons false ω)))^2 ≤ p 0*(1-p 0)*(C 0)^2+tailBound
    have h0 := mul_le_mul_of_nonneg_left (hb false) (sub_nonneg.mpr (hp1 0))
    have h1 := mul_le_mul_of_nonneg_left (hb true) (hp0 0)
    have h2 := mul_le_mul_of_nonneg_left hmsq (mul_nonneg (hp0 0) (sub_nonneg.mpr (hp1 0)))
    nlinarith only [h0, h1, h2]

end MetricKMedian.FiniteLaw
end
end

end OAI
