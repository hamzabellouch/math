import Mathlib
import OAI.Combinatorics.KMedian.Probability.BernoulliVariance

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

private def bitsEquiv (e : I ≃ J) : (J → Bool) ≃ (I → Bool) where
  toFun ω := ω ∘ e
  invFun ω := ω ∘ e.symm
  left_inv ω := by funext i; simp
  right_inv ω := by funext i; simp

theorem bernoulli_expect_equiv (e : I ≃ J) (p : I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (f : (I → Bool) → ℝ) :
    (bernoulli p hp0 hp1).expect f =
      (bernoulli (fun j => p (e.symm j)) (fun j => hp0 (e.symm j))
        (fun j => hp1 (e.symm j))).expect (fun ω => f (ω ∘ e)) := by
  unfold expect bernoulli
  rw [← (bitsEquiv e).sum_comp]
  apply Finset.sum_congr rfl
  intro ω _
  change (∏ i, coinWeight (p i) (ω (e i)))*f (ω ∘ e)=_
  have he := e.prod_comp (fun j => coinWeight (p (e.symm j)) (ω j))
  simp only [Equiv.symm_apply_apply] at he
  rw [he]

theorem bernoulli_variance_equiv (e : I ≃ J) (p : I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (f : (I → Bool) → ℝ) :
    (bernoulli p hp0 hp1).variance f =
      (bernoulli (fun j => p (e.symm j)) (fun j => hp0 (e.symm j))
        (fun j => hp1 (e.symm j))).variance (fun ω => f (ω ∘ e)) := by
  simp only [variance_eq,bernoulli_expect_equiv e p hp0 hp1]

theorem bernoulli_variance_bounded_differences_fintype
    (p C : I → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hC : ∀ i, 0 ≤ C i) (f : (I → Bool) → ℝ)
    (hdiff : ∀ i ω, |f (Function.update ω i true)-f (Function.update ω i false)| ≤ C i) :
    (bernoulli p hp0 hp1).variance f ≤ ∑ i, p i*(1-p i)*(C i)^2 := by
  let e := Fintype.equivFin I
  rw [bernoulli_variance_equiv e]
  have hd : ∀ i ω,
      |f (Function.update ω i true ∘ e)-f (Function.update ω i false ∘ e)| ≤ C (e.symm i) := by
    intro i ω
    simpa only [Function.update_comp_equiv] using hdiff (e.symm i) (ω ∘ e)
  have hh := bernoulli_variance_bounded_differences (Fintype.card I)
    (fun i => p (e.symm i)) (fun i => C (e.symm i))
    (fun i => hp0 (e.symm i)) (fun i => hp1 (e.symm i)) (fun i => hC (e.symm i))
    (fun ω => f (ω ∘ e)) hd
  exact hh.trans_eq (e.symm.sum_comp (fun i => p i*(1-p i)*(C i)^2))

end MetricKMedian.FiniteLaw
end
end

end OAI
