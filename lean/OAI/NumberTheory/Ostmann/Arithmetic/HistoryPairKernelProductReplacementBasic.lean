import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairKernelProductReplacement

theorem abs_finset_prod_sub_prod_le_two_pow_sum {ι : Type*} (s : Finset ι)
    (u v : ι → ℝ) (hu : ∀i ∈ s, |u i| ≤ 2) (hv : ∀i ∈ s, |v i| ≤ 2) :
    |(∏i ∈ s, u i) - ∏i ∈ s, v i| ≤ 2^s.card * ∑i ∈ s, |u i-v i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hu' : ∀i ∈ s, |u i| ≤ 2 := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have hv' : ∀i ∈ s, |v i| ≤ 2 := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have hd := ih hu' hv'
    have hV : |∏i ∈ s, v i| ≤ 2^s.card := by
      rw [Finset.abs_prod]
      calc
        ∏i ∈ s, |v i| ≤ ∏_i ∈ s, (2:ℝ) :=
          Finset.prod_le_prod₀ (fun i _ => abs_nonneg (v i)) hv'
        _ = 2^s.card := by simp
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
      Finset.card_insert_of_notMem ha]
    calc
      |u a * (∏i ∈ s, u i) - v a * ∏i ∈ s, v i| =
          |u a * ((∏i ∈ s, u i) - ∏i ∈ s, v i) +
            (u a-v a) * ∏i ∈ s, v i| := by congr 1; ring
      _ ≤ |u a| * |(∏i ∈ s, u i) - ∏i ∈ s, v i| +
          |u a-v a| * |∏i ∈ s, v i| := by
        simpa only [abs_mul] using abs_add_le
          (u a * ((∏i ∈ s, u i) - ∏i ∈ s, v i))
          ((u a-v a) * ∏i ∈ s, v i)
      _ ≤ 2 * (2^s.card * ∑i ∈ s, |u i-v i|) + |u a-v a| * 2^s.card :=
        add_le_add
          (mul_le_mul (hu a (Finset.mem_insert_self a s)) hd (abs_nonneg _) (by norm_num))
          (mul_le_mul_of_nonneg_left hV (abs_nonneg _))
      _ ≤ 2^(s.card+1) * (|u a-v a| + ∑i ∈ s, |u i-v i|) := by
        rw [pow_succ]
        nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) s.card)
          (abs_nonneg (u a-v a))]

theorem abs_prod_sub_prod_le_two_pow_sum {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (hu : ∀i, |u i| ≤ 2) (hv : ∀i, |v i| ≤ 2) :
    |(∏i, u i) - ∏i, v i| ≤ 2^(Fintype.card ι) * ∑i, |u i-v i| := by
  classical
  simpa only [Finset.card_univ] using
    abs_finset_prod_sub_prod_le_two_pow_sum Finset.univ u v
      (fun i _ => hu i) (fun i _ => hv i)

theorem weighted_product_error {ι : Type*} [Fintype ι]
    (p f g δ : ι → ℝ) (hp : ∀i, 0 ≤ p i) (hf : ∀i, 0 ≤ f i) (hg : ∀i, 0 ≤ g i)
    (hpf : ∀i, p i*f i ≤ 2) (hpg : ∀i, p i*g i ≤ 2)
    (_hδ : ∀i, 0 ≤ δ i) (herr : ∀i, p i*|f i-g i| ≤ 4*δ i) :
    (∏i, p i) * |(∏i, f i) - ∏i, g i| ≤ 4 * 2^(Fintype.card ι) * ∑i, δ i := by
  classical
  have h := abs_prod_sub_prod_le_two_pow_sum (fun i => p i*f i) (fun i => p i*g i)
    (fun i => by rw [abs_of_nonneg (mul_nonneg (hp i) (hf i))]; exact hpf i)
    (fun i => by rw [abs_of_nonneg (mul_nonneg (hp i) (hg i))]; exact hpg i)
  calc
    (∏i, p i) * |(∏i, f i) - ∏i, g i| = |(∏i, p i*f i) - ∏i, p i*g i| := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ←mul_sub, abs_mul,
        abs_of_nonneg (Finset.prod_nonneg (fun i _ => hp i))]
    _ ≤ 2^(Fintype.card ι) * ∑i, |p i*f i-p i*g i| := h
    _ ≤ 2^(Fintype.card ι) * ∑i, 4*δ i := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
      apply Finset.sum_le_sum
      intro i _
      rw [←mul_sub, abs_mul, abs_of_nonneg (hp i)]
      exact herr i
    _ = 4 * 2^(Fintype.card ι) * ∑i, δ i := by rw [←Finset.mul_sum]; ring

theorem weighted_product_error_mul_norm {ι : Type*} [Fintype ι]
    (p f g δ : ι → ℝ) (hp : ∀i, 0 ≤ p i) (hf : ∀i, 0 ≤ f i) (hg : ∀i, 0 ≤ g i)
    (hpf : ∀i, p i*f i ≤ 2) (hpg : ∀i, p i*g i ≤ 2)
    (hδ : ∀i, 0 ≤ δ i) (herr : ∀i, p i*|f i-g i| ≤ 4*δ i) (A : ℂ) :
    (∏i, p i) * ‖A * ((∏i, f i : ℝ):ℂ) - A * ((∏i, g i : ℝ):ℂ)‖ ≤
      ‖A‖ * (4 * 2^(Fintype.card ι) * ∑i, δ i) := by
  have h := mul_le_mul_of_nonneg_left
    (weighted_product_error p f g δ hp hf hg hpf hpg hδ herr) (norm_nonneg A)
  calc
    (∏i, p i) * ‖A * ((∏i, f i : ℝ):ℂ) - A * ((∏i, g i : ℝ):ℂ)‖ =
        ‖A‖ * ((∏i, p i) * |(∏i, f i) - ∏i, g i|) := by
      rw [←mul_sub, ←Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    _ ≤ ‖A‖ * (4 * 2^(Fintype.card ι) * ∑i, δ i) := h

end Ostmann.Arithmetic.HistoryPairKernelProductReplacement

end

end OAI
