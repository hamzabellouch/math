import OAI.NumberTheory.Ostmann.Supply.GroupedCharactersTransform
import OAI.NumberTheory.Ostmann.Supply.UnitWeightPolynomial

namespace OAI

noncomputable section
namespace Ostmann.Supply.GroupedCharacters
open Finset BivariateTruncation
open scoped BigOperators ComplexConjugate

theorem norm_rectangularTruncation_le (c : (ℕ × ℕ) →₀ ℂ) {r M : ℝ} (hr : 1 < r)
    (hM0 : 0 ≤ M) (hM : ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = r → ‖eval c u v‖ ≤ M) (K : ℕ) :
    ‖rectangularTruncation c K‖ ≤ M / (1 - r⁻¹)^2 := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  let s := c.support.filter (fun ij => ij.1 ≤ K ∧ ij.2 ≤ K)
  calc
    _ ≤ ∑ ij ∈ s, ‖c ij‖ := norm_sum_le _ _
    _ ≤ ∑ ij ∈ s, M * (r⁻¹)^(ij.1+ij.2) := by
      apply sum_le_sum
      intro ij hij
      simpa only [inv_pow, div_eq_mul_inv] using coefficient_norm_le c hr0 hM ij.1 ij.2
    _ = M * ∑ ij ∈ s, (r⁻¹)^(ij.1+ij.2) := (mul_sum _ _ _).symm
    _ ≤ M * (1 / (1-r⁻¹)^2) := mul_le_mul_of_nonneg_left
      (geometric_pair_sum_le (inv_nonneg.mpr hr0.le) ((inv_lt_one₀ hr0).mpr hr) s) hM0
    _ = _ := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) [∀ i, Fact (p i).Prime] (S : ∀ i, Finset (ZMod (p i)))
local instance (i : ι) : Fintype (MulChar (ZMod (p i)) ℂ) := Fintype.ofFinite _

theorem localWeightCoefficient_one (K : ℕ) :
    weightCoefficient (fun i => ZMod (p i)) (fun i => localKernel (S i) sparseKernelScale) K 1 =
      rectangularTruncation (unitWeightPolynomial p S) K := by
  rw [weightCoefficient, coefficient_one, truncation_unitWeightPolynomial]
  push_cast
  rfl

theorem norm_localWeightCoefficient_le (K : ℕ) (ρ : ∀ i, MulChar (ZMod (p i)) ℂ)
    (hlo : ∀ i, (1/3 : ℝ) ≤ density (S i)) (hhi : ∀ i, density (S i) ≤ 2/3)
    (hg : ∀ i, gamma (S i) ≤ supplyEpsilon^2) :
    ‖weightCoefficient (fun i => ZMod (p i))
      (fun i => localKernel (S i) sparseKernelScale) K ρ‖ ≤
      1200 * Real.exp (8*supplyEpsilon*(∑ i, 1/(p i : ℝ))) := by
  let M := Real.exp (8*supplyEpsilon*(∑ i, 1/(p i : ℝ)))
  have ht := norm_rectangularTruncation_le (unitWeightPolynomial p S)
    (show (1 : ℝ) < 103/100 by norm_num) (Real.exp_pos _).le
    (fun u v hu hv => unitWeightPolynomial_norm_uniform p S u v hlo hhi hg hu.le hv.le) K
  have hn : 0 ≤ (Fintype.card (∀ i, (ZMod (p i))ˣ) : ℝ)⁻¹ *
      ∑ x : ∀ i, (ZMod (p i))ˣ,
        truncatedWeight univ (fun i => localKernel (S i) sparseKernelScale (x i)) K := by
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (sum_nonneg (fun x hx => truncatedWeight_nonneg _ _ _))
  have hmean := norm_weightCoefficient_le_mean (fun i => ZMod (p i))
    (fun i => localKernel (S i) sparseKernelScale) K ρ
  have he : (Fintype.card (∀ i, (ZMod (p i))ˣ) : ℝ)⁻¹ *
      ∑ x : ∀ i, (ZMod (p i))ˣ,
        truncatedWeight univ (fun i => localKernel (S i) sparseKernelScale (x i)) K =
      ‖rectangularTruncation (unitWeightPolynomial p S) K‖ := by
    rw [truncation_unitWeightPolynomial, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  rw [he] at hmean
  apply hmean.trans (ht.trans _)
  change M / (1 - (103/100 : ℝ)⁻¹)^2 ≤ 1200*M
  have hM : 0 ≤ M := (Real.exp_pos _).le
  norm_num
  nlinarith

theorem norm_localWeightCoefficient_le_exp (K : ℕ) (ρ : ∀ i, MulChar (ZMod (p i)) ℂ)
    (hlo : ∀ i, (1/3 : ℝ) ≤ density (S i)) (hhi : ∀ i, density (S i) ≤ 2/3)
    (hg : ∀ i, gamma (S i) ≤ supplyEpsilon^2) {L D : ℝ} (hL : 1 ≤ L)
    (hH : (∑ i, 1/(p i : ℝ)) ≤ D*L) :
    ‖weightCoefficient (fun i => ZMod (p i))
      (fun i => localKernel (S i) sparseKernelScale) K ρ‖ ≤
      Real.exp ((1200 + 8*supplyEpsilon*D)*L) := by
  apply (norm_localWeightCoefficient_le p S K ρ hlo hhi hg).trans
  have h1200 : (1200 : ℝ) ≤ Real.exp 1200 := by linarith [Real.add_one_le_exp (1200 : ℝ)]
  calc
    _ ≤ Real.exp 1200 * Real.exp (8*supplyEpsilon*(∑ i, 1/(p i : ℝ))) :=
      mul_le_mul_of_nonneg_right h1200 (Real.exp_pos _).le
    _ = Real.exp (1200+8*supplyEpsilon*(∑ i, 1/(p i : ℝ))) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hH (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) supplyEpsilon_pos.le)
      nlinarith

end Ostmann.Supply.GroupedCharacters

end

end OAI
