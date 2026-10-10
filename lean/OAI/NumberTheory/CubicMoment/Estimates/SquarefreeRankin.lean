import OAI.NumberTheory.CubicMoment.Estimates.SieveMobius
import OAI.NumberTheory.CubicMoment.Estimates.PrimeReciprocal

namespace OAI

/-! Finite Rankin bounds for the actual primary squarefree elements.
The map to their prime-factor subsets is injective; no ideal-counting
or smooth-number estimate is assumed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_supported_rankin_sum (S U : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hU : ∀ b ∈ S, primaryPrimeFactors b ⊆ U) (σ : ℝ) :
    (∑ b ∈ S, norm b^(-σ)) ≤ ∏ p ∈ U, (1+norm p^(-σ)) := by
  rw [Finset.prod_one_add]
  apply Finset.sum_le_sum_of_injOn primaryPrimeFactors
  · intro b hb c hc he
    calc
      b = ∏ p ∈ primaryPrimeFactors b, p := (primaryPrimeFactors_prod (hS b hb).1 (hS b hb).2).symm
      _ = ∏ p ∈ primaryPrimeFactors c, p := by rw [he]
      _ = c := primaryPrimeFactors_prod (hS c hc).1 (hS c hc).2
  · intro s hs
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_powerset.mpr (hU b hb)
  · intro b hb
    have hn : norm b = ∏ p ∈ primaryPrimeFactors b, norm p := by
      rw [←norm_finset_prod,primaryPrimeFactors_prod (hS b hb).1 (hS b hb).2]
    rw [hn,Real.finsetProd_rpow _ _ (fun p _ => norm_nonneg p)]
  · intro s hs hnot
    exact Finset.prod_nonneg (fun p _ => Real.rpow_nonneg (norm_nonneg p) _)

lemma squarefree_supported_rankin_card (S U : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hU : ∀ b ∈ S, primaryPrimeFactors b ⊆ U)
    {B σ : ℝ} (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hsize : ∀ b ∈ S, norm b ≤ B) :
    (S.card:ℝ) ≤ B^σ*∏ p ∈ U, (1+norm p^(-σ)) := by
  calc
    _ = ∑ _b ∈ S, (1:ℝ) := by simp
    _ ≤ ∑ b ∈ S, B^σ*norm b^(-σ) := by
      apply Finset.sum_le_sum
      intro b hb
      have hb0 := norm_pos_of_ne_zero (primary_ne_zero (hS b hb).1)
      calc
        1 = norm b^σ*norm b^(-σ) := by
          rw [←Real.rpow_add hb0,add_neg_cancel,Real.rpow_zero]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hb0.le (hsize b hb) hσ) (Real.rpow_nonneg hb0.le _)
    _ = B^σ*∑ b ∈ S, norm b^(-σ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (squarefree_supported_rankin_sum S U hS hU σ)
      (Real.rpow_nonneg hB _)

lemma finite_euler_product_le_exp (U : Finset Eisenstein) (σ : ℝ) :
    (∏ p ∈ U, (1+norm p^(-σ))) ≤ Real.exp (∑ p ∈ U, norm p^(-σ)) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact add_nonneg zero_le_one (Real.rpow_nonneg (norm_nonneg p) _)
  · intro p hp
    simpa only [add_comm] using Real.add_one_le_exp (norm p^(-σ))

lemma shifted_prime_reciprocal_le {y : ℝ} (hy : 1 < y)
    {p : Eisenstein} (hp : primaryPrime p) (hpy : norm p ≤ y) :
    norm p^(-1+(Real.log y)⁻¹) ≤ Real.exp 1*(norm p)⁻¹ := by
  have hp0 := norm_pos_of_ne_zero hp.2.ne_zero
  have hl : 0 < Real.log y := Real.log_pos hy
  have hpower : y^((Real.log y)⁻¹) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hy),mul_inv_cancel₀ hl.ne']
  rw [Real.rpow_add hp0,Real.rpow_neg_one]
  calc
    _ ≤ (norm p)⁻¹*y^((Real.log y)⁻¹) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hp0.le hpy (inv_nonneg.mpr hl.le)) (inv_nonneg.mpr hp0.le)
    _ = _ := by rw [hpower,mul_comm]

theorem smooth_squarefree_rankin_bound (S : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b) {B y : ℝ}
    (hB : 0 ≤ B) (hy : Real.exp 1 ≤ y) (hsize : ∀ b ∈ S, norm b ≤ B)
    (hsmooth : ∀ b ∈ S, ∀ p ∈ primaryPrimeFactors b, norm p ≤ y) :
    (S.card:ℝ) ≤ B^(1-(Real.log y)⁻¹)*
      Real.exp (Real.exp 1*∑ p ∈ primeCutoff y, (norm p)⁻¹) := by
  have hy1 : 1 < y := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 1)).trans_le hy
  have hl : 1 ≤ Real.log y := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hy
  have hσ : 0 ≤ 1-(Real.log y)⁻¹ := sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr hl)
  have hsub : ∀ b ∈ S, primaryPrimeFactors b ⊆ primeCutoff y := by
    intro b hb p hp
    exact mem_primeCutoff.mpr ⟨(primaryPrimeFactor_spec (hS b hb).1 hp).1,hsmooth b hb p hp⟩
  apply (squarefree_supported_rankin_card S (primeCutoff y) hS hsub hB hσ hsize).trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hB _)
  apply (finite_euler_product_le_exp (primeCutoff y) (1-(Real.log y)⁻¹)).trans
  apply Real.exp_le_exp.mpr
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  convert shifted_prime_reciprocal_le hy1 (mem_primeCutoff.mp hp).1
    (mem_primeCutoff.mp hp).2 using 1; congr 1; ring

end CubicFirstMoment

end

end OAI
