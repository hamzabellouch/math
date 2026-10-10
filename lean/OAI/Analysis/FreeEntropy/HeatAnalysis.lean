import OAI.Analysis.FreeEntropy.EntropyFiniteness

namespace OAI

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set Finset
namespace FiniteEntropySeparation
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
def heatFisherReal (u : ℝ) : ℝ := (freeFisher (τ p) (X p u)).toReal
 theorem heatFisher_ne_top (u : ℝ) (hu : 0 < u) : freeFisher (τ p) (X p u) ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (heat_freeFisher_le ∅ (C p) (C_mem_background p ∅) (initialIndex p)
      (initialIndex_injective p) (by simp) u hu)
 theorem heatFisherReal_upper (u : ℝ) (hu : 0 < u) : heatFisherReal p u ≤ (p+1 : ℕ)/u := by
  have he := heat_freeFisher_le ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp) u hu
  exact (ENNReal.toReal_le_toReal (heatFisher_ne_top p u hu) ENNReal.ofReal_ne_top).mpr he |>.trans_eq
    (ENNReal.toReal_ofReal (by positivity))
 theorem heatFisherReal_lower (u : ℝ) (hu : 0 < u) : covarianceFisher p u ≤ heatFisherReal p u := by
  obtain ⟨ξ,hξ⟩ := heat_conjugates_exist ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp) u hu
  change ConjugateSystem (τ p) (X p u) ξ at hξ
  unfold heatFisherReal
  rw [freeFisher_eq_of_conjugate _ hξ, ENNReal.toReal_ofReal (sum_nonneg (fun _ _ => sq_nonneg _))]
  apply sum_le_sum
  intro i _
  simpa only [X_variance p u hu.le, one_div] using conjugate_norm_sq_lower (τ p) hξ i
 theorem heatFisherReal_measurable : Measurable (fun u : Ioi (0 : ℝ) => heatFisherReal p u) :=
  ENNReal.measurable_toReal.comp (heat_freeFisher_measurable ∅ (C p) (C_mem_background p ∅)
    (initialIndex p) (initialIndex_injective p) (by simp))
 theorem heatFisherReal_shift_aesm (a : ℝ) (ha : 0 < a) :
    AEStronglyMeasurable (fun s => heatFisherReal p (a+s)) (volume.restrict (Ioi 0)) := by
  let g : ℝ → Ioi (0 : ℝ) := fun s => ⟨a+max s 0, by exact lt_of_lt_of_le ha (le_add_of_nonneg_right (le_max_right s 0))⟩
  have hg : Continuous g := by continuity
  have hm := ((heatFisherReal_measurable p).comp hg.measurable).aestronglyMeasurable (μ := volume.restrict (Ioi 0))
  apply hm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change heatFisherReal p (a+max s 0) = _
  rw [max_eq_left (le_of_lt hs)]
 theorem fisherDeficit_nonneg (u : ℝ) (hu : 0 < u) : 0 ≤ fisherDeficit p u :=
  sub_nonneg.mpr (heatFisherReal_lower p u hu)
 theorem fisherDeficit_upper (hp : 2 ≤ p) (u : ℝ) (hu : 0 < u) :
    fisherDeficit p u ≤ (p+1 : ℕ)/u^2 := by
  have he (i : Fin (p+1)) : u⁻¹ - (variance p i + u)⁻¹ ≤ u⁻¹^2 := by
    have hv := variance_nonneg p i
    have hv1 := variance_le_one p hp i
    have hd : 0 < variance p i + u := by linarith
    have hi := one_div_le_one_div_of_le hu (by linarith : u ≤ variance p i + u)
    have hid : (variance p i + u)⁻¹ ≤ u⁻¹ := by simpa only [one_div] using hi
    have heq : u⁻¹ - (variance p i + u)⁻¹ = variance p i * u⁻¹ * (variance p i+u)⁻¹ := by
      field_simp; ring
    rw [heq]
    calc
      _ ≤ 1 * u⁻¹ * u⁻¹ := mul_le_mul (mul_le_mul_of_nonneg_right hv1 (by positivity)) hid
        (by positivity) (by positivity)
      _ = _ := by ring
  change heatFisherReal p u - covarianceFisher p u ≤ _
  calc
    _ ≤ (p+1 : ℕ)/u - covarianceFisher p u := sub_le_sub_right (heatFisherReal_upper p u hu) _
    _ = ∑ i : Fin (p+1), (u⁻¹ - (variance p i + u)⁻¹) := by
      simp [covarianceFisher, sum_sub_distrib, div_eq_mul_inv]
    _ ≤ ∑ _i : Fin (p+1), u⁻¹^2 := sum_le_sum (fun i _ => he i)
    _ = _ := by simp [div_eq_mul_inv, inv_pow]
 theorem heatFisherReal_broad_lower (hp : 2 ≤ p) (u : ℝ) (hu : 0 < u) :
    (p+1 : ℕ)/(u+4) ≤ heatFisherReal p u := by
  apply le_trans _ (heatFisherReal_lower p u hu)
  have he (i : Fin (p+1)) : 1/(u+4) ≤ (variance p i+u)⁻¹ := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by linarith [variance_nonneg p i])
      (by linarith [variance_le_one p hp i])
  simpa [covarianceFisher, div_eq_mul_inv] using sum_le_sum (s := (univ : Finset (Fin (p+1)))) (fun i _ => he i)
 theorem entropyIntegrand_integrable (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s => (p+1 : ℕ)/(1+s) - heatFisherReal p (a+s)) (Ioi 0) := by
  have hm : AEStronglyMeasurable (fun s : ℝ => (p+1 : ℕ)/(1+s)) (volume.restrict (Ioi 0)) := by
    exact (by fun_prop : Measurable (fun s : ℝ => (p+1 : ℕ)/(1+s))).aestronglyMeasurable
  apply integrable_of_le_of_le (hm.sub (heatFisherReal_shift_aesm p a ha))
    (g₁ := fun s => (p+1 : ℕ) * reciprocalDifference a s)
    (g₂ := fun s => (p+1 : ℕ) * reciprocalDifference (a+4) s)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have he := heatFisherReal_upper p (a+s) (by linarith [show 0<s from hs])
    dsimp [reciprocalDifference]
    simp only [mul_sub, mul_one_div]
    linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have he := heatFisherReal_broad_lower p hp (a+s) (by linarith [show 0<s from hs])
    dsimp [reciprocalDifference]
    simp only [mul_sub, mul_one_div]
    convert sub_le_sub_left he ((p+1 : ℕ)/(1+s)) using 1 ; congr 2 ; ring
  · exact (reciprocalDifference_integrable ha).const_mul _
  · exact (reciprocalDifference_integrable (by linarith : 0 < a+4)).const_mul _
end Model
end FiniteEntropySeparation

end

end OAI
