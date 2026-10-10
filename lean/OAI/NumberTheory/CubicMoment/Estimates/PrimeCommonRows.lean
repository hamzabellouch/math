import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeOverlapEnergy
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeMellin
import OAI.NumberTheory.CubicGram.SieveMajorant

namespace OAI

/-! Arithmetic bounds for the actual common-factor quotient rows. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullPrime_residual_norms {R L : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hprod : (∏ i, X i) = L)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (e : Eisenstein) {k a : Eisenstein} (hk : k ≠ 0)
    (ha : a ∈ residualRows (fullSquarefreePrimeSupport R W X e) k) :
    L/norm k ≤ norm a ∧ norm a ≤ R^Fintype.card ι*L/norm k := by
  have hab := (mem_residualRows hk).mp ha
  have hn := fullPrimeProduct_norm_bounds R W X hX hlo hhi (Finset.mem_filter.mp hab).1
  rw [hprod,norm_mul_eq] at hn
  have hkN := norm_pos_of_ne_zero hk
  exact ⟨(div_le_iff₀ hkN).mpr (by nlinarith [hn.1]),
    (le_div_iff₀ hkN).mpr (by nlinarith [hn.2])⟩

lemma fullPrime_nonunit_common_factor_large {R D : ℝ}
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e : Eisenstein) {k : Eisenstein}
    (hk : k ∈ commonRowFactors (fullSquarefreePrimeSupport R W X e)) (hk1 : k ≠ 1) :
    D < norm k := by
  have hS : ∀ a ∈ fullSquarefreePrimeSupport R W X e, primary a ∧ Squarefree a :=
    fun a ha => fullSquarefreePrimeSupport_primary R W X e ha
  have hks := commonRowFactors_spec hS hk
  have hpnonempty : (primaryPrimeFactors k).Nonempty := by
    by_contra hn
    have he := primaryPrimeFactors_prod hks.1 hks.2
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.prod_empty] at he
    exact hk1 he.symm
  obtain ⟨⟨a,b⟩,hab,hprod⟩ := Finset.mem_image.mp hk
  have ha := (Finset.mem_product.mp hab).1
  have hb := (Finset.mem_product.mp hab).2
  have hkd : k ∣ a := hprod ▸
    (primaryCommonFactor_spec (hS a ha).1 (hS b hb).1 (hS a ha).2 (hS b hb).2).2.2.1
  have hprodK := primaryPrimeFactors_prod hks.1 hks.2
  rw [← hprodK]
  exact fullPrime_nonempty_divisor_large W X hX hlo hhi hrough (primaryPrimeFactors k)
    (fun p hp => (primaryPrimeFactor_spec hks.1 hp).1) hpnonempty
    (Finset.mem_filter.mp ha).1 (hprodK.symm ▸ hkd)

lemma fullPrime_common_energy_bound (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) (v : Eisenstein → ℂ) :
    (∑ k ∈ commonRowFactors (fullSquarefreePrimeSupport R W X e),
      (2:ℝ)^(primaryPrimeFactors k).card *
        commonBlockEnergy (fullSquarefreePrimeSupport R W X e) v k) ≤
      (2:ℝ)^(3*Fintype.card ι) *
        ∑ a ∈ fullSquarefreePrimeSupport R W X e, ‖v a‖^2 := by
  have hS : ∀ a ∈ fullSquarefreePrimeSupport R W X e, primary a ∧ Squarefree a :=
    fun a ha => fullSquarefreePrimeSupport_primary R W X e ha
  apply (common_energy_cubic_weight _ hS v).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hc : (primaryPrimeFactors a).card ≤ Fintype.card ι :=
    primeProduct_primeFactors_card _ (fullPrimeSupport_prime R W X) (Finset.mem_filter.mp ha).1
  rw [← pow_mul]
  apply pow_le_pow_right₀ (by norm_num)
  omega

end CubicFirstMoment

end

end OAI
