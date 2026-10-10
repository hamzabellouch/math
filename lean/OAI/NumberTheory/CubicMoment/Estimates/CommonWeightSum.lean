import OAI.NumberTheory.CubicMoment.Estimates.IdealDivisorPower
import OAI.NumberTheory.CubicMoment.Estimates.SieveMobius
import OAI.NumberTheory.CubicMoment.Estimates.NormSeries

namespace OAI

/-! The summable common-factor weight needed after the low-height estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_factor_power_small_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Eisenstein, primary a →
      (2:ℝ)^(primaryPrimeFactors a).card ≤ C*norm a^ε := by
  obtain ⟨C,hC,hdiv⟩ := primary_divisor_card_small_power hε
  refine ⟨C,hC,?_⟩
  intro a ha
  let U := primaryPrimeFactors a
  let P := U.powerset.image (fun s => ∏ p ∈ s, p)
  have hU : ∀ p ∈ U, primaryPrime p := fun p hp => (primaryPrimeFactor_spec ha hp).1
  have hP : ∀ d ∈ P, primary d := by
    intro d hd
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hd
    exact primary_finset_prod _ _ (fun p hp => (hU p (Finset.mem_powerset.mp hs hp)).1)
  have hdvd : ∀ d ∈ P, d ∣ a := by
    intro d hd
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hd
    exact (primary_subsets_prod_dvd ha (Finset.mem_powerset.mp hs) a).mpr
      (fun p hp => (primaryPrimeFactor_spec ha (Finset.mem_powerset.mp hs hp)).2)
  have he : P.filter (fun d => d ∣ a) = P := Finset.filter_eq_self.mpr hdvd
  have hc : P.card = 2^U.card := by
    exact (Finset.card_image_of_injOn (primaryPrimeFactors_prod_injective hU)).trans
      (Finset.card_powerset U)
  have hh := hdiv P hP a (primary_ne_zero ha)
  rw [he,hc] at hh
  exact_mod_cast hh

lemma common_factor_weight_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Finset Eisenstein, (∀ a ∈ I, primary a) →
      (∑ a ∈ I, (2:ℝ)^(primaryPrimeFactors a).card*norm a^(-(5/3:ℝ))) ≤ C := by
  obtain ⟨D,hD,hbound⟩ := prime_factor_power_small_bound (by norm_num : (0:ℝ) < 1/3)
  have hs := summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 4/3)
  let R := ∑' a : Eisenstein, norm a^(-(4/3:ℝ))
  have hR : 0 ≤ R := tsum_nonneg (fun a => Real.rpow_nonneg (norm_nonneg a) _)
  refine ⟨D*(1+R),by positivity,?_⟩
  intro I hI
  calc
    _ ≤ ∑ a ∈ I, D*norm a^(-(4/3:ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      have hn := norm_pos_of_ne_zero (primary_ne_zero (hI a ha))
      calc
        _ ≤ (D*norm a^(1/3:ℝ))*norm a^(-(5/3:ℝ)) :=
          mul_le_mul_of_nonneg_right (hbound a (hI a ha)) (by positivity)
        _ = _ := by rw [mul_assoc,←Real.rpow_add hn]; norm_num
    _ = D*(∑ a ∈ I, norm a^(-(4/3:ℝ))) := (Finset.mul_sum _ _ _).symm
    _ ≤ D*R := mul_le_mul_of_nonneg_left (hs.sum_le_tsum I (fun a _ => Real.rpow_nonneg (norm_nonneg a) _)) hD.le
    _ ≤ D*(1+R) := by nlinarith

end CubicFirstMoment

end

end OAI
