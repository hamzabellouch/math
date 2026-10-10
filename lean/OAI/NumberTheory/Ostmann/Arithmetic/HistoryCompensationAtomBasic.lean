import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationMomentBasic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationAtom
open HistoryCompensationMoment
variable {ι κ : Type*} [Fintype ι]

def blockWeight (μ : ι → κ → ℝ) (v : κ → ℝ) (x : κ) : ℝ :=
  (v x)⁻¹ * ∏ i, μ i x * v x

lemma blockWeight_nonneg (μ : ι → κ → ℝ) (v : κ → ℝ)
    (hμ : ∀ i x, 0 ≤ μ i x) (hv : ∀ x, 0 ≤ v x) (x : κ) :
    0 ≤ blockWeight μ v x :=
  mul_nonneg (inv_nonneg.mpr (hv x))
    (Finset.prod_nonneg (fun i _ => mul_nonneg (hμ i x) (hv x)))

lemma blockWeight_eq_zero_of_mass_eq_zero (μ : ι → κ → ℝ) (v : κ → ℝ)
    (j : ι) (x : κ) (hj : μ j x = 0) : blockWeight μ v x = 0 := by
  have hh : (∏ i, μ i x * v x) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, zero_mul])
  simp only [blockWeight, hh, mul_zero]

lemma blockWeight_le_reciprocal_cap (μ : ι → κ → ℝ) (v : κ → ℝ) (C : ι → ℝ)
    (hμ : ∀ i x, 0 ≤ μ i x) (hv : ∀ x, 0 ≤ v x)
    (hcap : ∀ i x, μ i x * v x ≤ C i) (x : κ) :
    blockWeight μ v x ≤ (v x)⁻¹ * ∏ i, C i := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hv x))
  exact Finset.prod_le_prod₀ (fun i _ => mul_nonneg (hμ i x) (hv x))
    (fun i _ => hcap i x)

theorem blockWeight_atom_le (μ : ι → κ → ℝ) (v : κ → ℝ) (C : ι → ℝ)
    (j : ι) (H : ℝ) (hμ : ∀ i x, 0 ≤ μ i x) (hv : ∀ x, 0 < v x)
    (hC : ∀ i, 0 ≤ C i) (hcap : ∀ i x, μ i x * v x ≤ C i)
    (hsource : ∀ x, μ j x ≠ 0 → H ≤ Real.log (v x)) (x : κ) :
    blockWeight μ v x ≤ Real.exp (-H) * ∏ i, C i := by
  by_cases hj : μ j x = 0
  · rw [blockWeight_eq_zero_of_mass_eq_zero μ v j x hj]
    exact mul_nonneg (Real.exp_nonneg _) (Finset.prod_nonneg (fun i _ => hC i))
  · have hlo : Real.exp H ≤ v x := by
      simpa only [Real.exp_log (hv x)] using Real.exp_le_exp.mpr (hsource x hj)
    have hi : (v x)⁻¹ ≤ Real.exp (-H) := by
      have hh := one_div_le_one_div_of_le (Real.exp_pos H) hlo
      simpa only [one_div, Real.exp_neg] using hh
    exact (blockWeight_le_reciprocal_cap μ v C hμ (fun x => (hv x).le) hcap x).trans
      (mul_le_mul_of_nonneg_right hi (Finset.prod_nonneg (fun i _ => hC i)))

variable [DecidableEq ι] [Fintype κ]

theorem blockWeight_mass_le (μ : ι → κ → ℝ) (v : κ → ℝ) (C : ι → ℝ)
    (j : ι) (hμ : ∀ i x, 0 ≤ μ i x) (hv : ∀ x, 0 < v x)
    (hcap : ∀ i x, μ i x * v x ≤ C i) (hnorm : ∑ x, μ j x = 1) :
    (∑ x, blockWeight μ v x) ≤ ∏ i ∈ Finset.univ.erase j, C i :=
  block_moment_le μ v C j hμ hv hcap hnorm

end Ostmann.Arithmetic.HistoryCompensationAtom

end

end OAI
