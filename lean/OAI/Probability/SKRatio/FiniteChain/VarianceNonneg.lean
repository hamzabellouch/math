import Mathlib
import OAI.Probability.SKRatio.FiniteChain.Mean

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio.FiniteLaw
variable {α : Type*} [Fintype α]

theorem variance_nonneg (p f : α → ℝ) (hp : ∀ x, 0 ≤ p x) :
    0 ≤ variance p f := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (sq_nonneg _))

theorem submass_centered_mean (p ρ f : α → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (hρp : ∀ x, ρ x ≤ p x) :
    |mean ρ (fun x => f x - mean p f)| ≤
      Real.sqrt (∑ x, ρ x) * Real.sqrt (variance p f) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun x => Real.sqrt (ρ x)) (fun x => Real.sqrt (ρ x) * |f x - mean p f|)
  simp only [mul_pow, Real.sq_sqrt (hρ _), sq_abs,
    ← mul_assoc, Real.mul_self_sqrt (hρ _)] at hcs
  calc
    |mean ρ (fun x => f x - mean p f)| ≤ ∑ x, |ρ x * (f x - mean p f)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, ρ x * |f x - mean p f| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (hρ x)]
    _ ≤ Real.sqrt (∑ x, ρ x) * Real.sqrt (∑ x, ρ x * (f x - mean p f) ^ 2) := hcs
    _ ≤ Real.sqrt (∑ x, ρ x) * Real.sqrt (variance p f) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hρp x) (sq_nonneg _))

theorem common_mass_means (p q f : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1)
    {ε : ℝ} (hε : 0 < ε) (hTV : totalVariation p q ≤ 1 - ε) :
    |mean p f - mean q f| ≤
      (Real.sqrt (variance p f) + Real.sqrt (variance q f)) / Real.sqrt ε := by
  let ρ := fun x => min (p x) (q x)
  let c : ℝ := ∑ x, ρ x
  have hρ : ∀ x, 0 ≤ ρ x := fun x => le_min (hp x) (hq x)
  have hpmean := submass_centered_mean p ρ f hρ (fun x => min_le_left _ _)
  have hqmean := submass_centered_mean q ρ f hρ (fun x => min_le_right _ _)
  have heq : c * (mean p f - mean q f) =
      mean ρ (fun x => f x - mean q f) - mean ρ (fun x => f x - mean p f) := by
    simp only [mean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, c]
    ring
  have hc : ε ≤ c := by
    dsimp only [c, ρ]
    rw [common_mass p q hp1 hq1]
    linarith only [hTV]
  have hc0 : 0 < c := hε.trans_le hc
  have htriangle : c * |mean p f - mean q f| ≤
      Real.sqrt c * (Real.sqrt (variance p f) + Real.sqrt (variance q f)) := by
    calc
      c * |mean p f - mean q f| = |c * (mean p f - mean q f)| := by
        rw [abs_mul, abs_of_pos hc0]
      _ ≤ |mean ρ (fun x => f x - mean q f)| + |mean ρ (fun x => f x - mean p f)| := by
        rw [heq]
        exact abs_sub _ _
      _ ≤ Real.sqrt c * Real.sqrt (variance q f) + Real.sqrt c * Real.sqrt (variance p f) :=
        add_le_add hqmean hpmean
      _ = _ := by ring
  have hb : Real.sqrt c * |mean p f - mean q f| ≤
      Real.sqrt (variance p f) + Real.sqrt (variance q f) := by
    apply (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr hc0)).mp
    simpa only [← mul_assoc, Real.mul_self_sqrt hc0.le] using htriangle
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hε)).mpr
  calc
    |mean p f - mean q f| * Real.sqrt ε ≤ |mean p f - mean q f| * Real.sqrt c :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hc) (abs_nonneg _)
    _ ≤ _ := by simpa only [mul_comm] using hb

theorem totalVariation_le_of_tests (p q : α → ℝ) {B : ℝ}
    (h : ∀ f : α → ℝ, (∀ x, |f x| ≤ 1) → |mean p f - mean q f| ≤ 2 * B) :
    totalVariation p q ≤ B := by
  let f : α → ℝ := fun x => if 0 ≤ p x - q x then 1 else -1
  have hf : ∀ x, |f x| ≤ 1 := by
    intro x
    dsimp only [f]
    split_ifs <;> norm_num
  have hprod (x : α) : (p x - q x) * f x = |p x - q x| := by
    dsimp only [f]
    split_ifs with h
    · rw [mul_one, abs_of_nonneg h]
    · rw [mul_neg_one, abs_of_neg (lt_of_not_ge h)]
  have hid : mean p f - mean q f = 2 * totalVariation p q := by
    simp only [mean, ← Finset.sum_sub_distrib, ← sub_mul, hprod, totalVariation]
    ring
  have hbound := h f hf
  rw [hid, abs_of_nonneg (mul_nonneg (by norm_num) (totalVariation_nonneg p q))] at hbound
  linarith only [hbound]

end SKRatio.FiniteLaw

end
end
end
end
end

end OAI
