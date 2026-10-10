import Mathlib

namespace OAI

noncomputable section
open Set
namespace YauCounterexamples

lemma cos_unit_quadratic_gap {s : ℝ} (hs : |s| ≤ 1) : s^2/4 ≤ 1-Real.cos s := by
  let f : ℝ → ℝ := fun t => 1-Real.cos t-t^2/4
  let f' : ℝ → ℝ := fun t => Real.sin t-t/2
  let f'' : ℝ → ℝ := fun t => Real.cos t-1/2
  have hd (t : ℝ) : HasDerivAt f (f' t) t := by
    convert ((hasDerivAt_const t (1 : ℝ)).sub (Real.hasDerivAt_cos t)).sub
      (((hasDerivAt_id t).pow 2).div_const 4) using 1 <;> first | rfl | (dsimp [f,f']; ring)
  have hdd (t : ℝ) : HasDerivAt f' (f'' t) t := by
    exact (Real.hasDerivAt_sin t).sub ((hasDerivAt_id t).div_const 2)
  have hc : ConvexOn ℝ (Icc (-1) 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => (hdd t).hasDerivWithinAt)
    intro t ht
    dsimp [f'']
    have ht := interior_subset ht
    have hsq : t^2 ≤ 1 := by
      have hp := mul_nonneg (sub_nonneg.mpr ht.2) (show 0 ≤ t+1 by linarith [ht.1])
      nlinarith
    have hcos := Real.one_sub_sq_div_two_le_cos (x := t)
    linarith
  have hmem : s ∈ Icc (-1 : ℝ) 1 := abs_le.mp hs
  have hneg : -s ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hmem.1,hmem.2]
  have hh := hc.2 hmem hneg (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (1/2 : ℝ)+1/2=1 by norm_num)
  dsimp [f] at hh
  simp only [Real.cos_neg,neg_sq] at hh
  rw [show (1/2 : ℝ)*s+1/2*(-s)=0 by ring,Real.cos_zero] at hh
  nlinarith

lemma common_weight_cosine_gap {I : Type*} [Fintype I]
    (weights : I → ℝ) (hweights : ∀ i, 0 ≤ weights i) (hsum : ∑ i, weights i = 1)
    (θ : I → Fin 3 → ℝ) {κ : ℝ}
    (hθ : ∀ i j, |θ i j| ≤ 1) (he : ∀ i, κ ≤ ∑ j, (θ i j)^2) :
    (∀ j, 1/2 ≤ ∑ i, weights i*Real.cos (θ i j)) ∧
      κ/4 ≤ ∑ j, (1-∑ i, weights i*Real.cos (θ i j)) := by
  classical
  constructor
  · intro j
    calc
      1/2 = ∑ i, weights i*(1/2) := by rw [←Finset.sum_mul,hsum]; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (by
        have hs : (θ i j)^2 ≤ 1 := by
          have hab := abs_le.mp (hθ i j)
          have hp := mul_nonneg (sub_nonneg.mpr hab.2) (show 0 ≤ θ i j+1 by linarith [hab.1])
          nlinarith
        linarith [Real.one_sub_sq_div_two_le_cos (x := θ i j)]) (hweights i))
  · calc
      κ/4 = ∑ i, weights i*(κ/4) := by rw [←Finset.sum_mul,hsum]; ring
      _ ≤ ∑ i, weights i*(∑ j, (1-Real.cos (θ i j))) := by
        apply Finset.sum_le_sum; intro i _
        apply mul_le_mul_of_nonneg_left _ (hweights i)
        apply (div_le_div_of_nonneg_right (he i) (by norm_num : (0 : ℝ) ≤ 4)).trans
        rw [Finset.sum_div]
        exact Finset.sum_le_sum (fun j _ => cos_unit_quadratic_gap (hθ i j))
      _ = _ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hsum]

end YauCounterexamples
end

end OAI
