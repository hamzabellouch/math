import OAI.Probability.InvariantIsing.Fields.FieldGaussianOrdinaryOrder

namespace OAI

/-! The radial payoff comparison propagates through each actual nonzero
Gaussian backward operator. The zero-exponent case is handled separately. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldFolded_exp_difference_mul (v ζ : ℝ) (F G : ℝ → ℝ) (z u : ℝ) :
    Real.exp (ζ * (G u - F u)) * fieldFoldedWeight v ζ F z u =
      fieldFoldedWeight v ζ G z u := by
  dsimp only [fieldFoldedWeight]
  calc
    _ = (Real.exp (-u ^ 2 / (2 * v)) * Real.cosh (z / v * u)) *
        (Real.exp (ζ * (G u - F u)) * Real.exp (ζ * F u)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

lemma fieldFolded_mass_ratio_monotone (v : ℝ) (hv : 0 < v) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (F G : ℝ → ℝ) (hFG : MonotoneOn (fun u => G u - F u) (Ici 0))
    (hF : ∀ z, Integrable (fieldFoldedWeight v ζ F z) (volume.restrict (Ici 0)))
    (hG : ∀ z, Integrable (fieldFoldedWeight v ζ G z) (volume.restrict (Ici 0)))
    (hFpos : ∀ z, 0 < ∫ u in Ici 0, fieldFoldedWeight v ζ F z u) :
    MonotoneOn (fun z => (∫ u in Ici 0, fieldFoldedWeight v ζ G z u) /
      (∫ u in Ici 0, fieldFoldedWeight v ζ F z u)) (Ici 0) := by
  intro x hx y _hy hxy
  have htest : MonotoneOn (fun u => Real.exp (ζ * (G u - F u))) (Ici 0) := by
    intro u hu v hv huv
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hFG hu hv huv) hζ)
  have hi (z : ℝ) : Integrable (fun u => Real.exp (ζ * (G u - F u)) *
      fieldFoldedWeight v ζ F z u) (volume.restrict (Ici 0)) := by
    simpa only [fieldFolded_exp_difference_mul] using hG z
  have h := field_likelihood_ratio_expectation_le (volume.restrict (Ici 0))
    (fieldFoldedWeight v ζ F x) (fieldFoldedWeight v ζ F y)
    (fun u => Real.exp (ζ * (G u - F u))) (ae_restrict_mem measurableSet_Ici) htest
    (fun u hu w _hw huw => fieldFoldedWeight_parent_order hv ζ F hx hxy hu huw)
    (hF x) (hF y) (hi x) (hi y) (hFpos x) (hFpos y)
  simpa only [fieldFolded_exp_difference_mul] using h

lemma field_gaussian_exp_ratio_folded (v : ℝ≥0) (hv : v ≠ 0) (ζ : ℝ)
    (F G : ℝ → ℝ) (hFeven : Function.Even F) (hGeven : Function.Even G)
    (z : ℝ)
    (hzF : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v))
    (hzG : Integrable (fun u => Real.exp (ζ * G u)) (gaussianReal z v)) :
    (∫ u, Real.exp (ζ * G u) ∂gaussianReal z v) /
      (∫ u, Real.exp (ζ * F u) ∂gaussianReal z v) =
    (∫ u in Ici 0, fieldFoldedWeight v ζ G z u) /
      (∫ u in Ici 0, fieldFoldedWeight v ζ F z u) := by
  have hnum := field_gaussian_folded_integral v hv z ζ G (fun _ => 1) hGeven
    (by simpa only [mul_one] using hzG)
  have hden := field_gaussian_folded_integral v hv z ζ F (fun _ => 1) hFeven
    (by simpa only [mul_one] using hzF)
  simp only [mul_one, one_mul] at hnum hden
  rw [hnum, hden, mul_div_mul_left _ _ (field_folded_constant_pos v hv z).ne']

/-- Increasing an even payoff by a radially increasing difference has a
radially increasing effect on the nonzero-exponent backward value. -/
theorem gaussianOperator_difference_monotone_pos (v : ℝ≥0) (hv : v ≠ 0)
    {ζ : ℝ} (hζ : 0 < ζ) (F G : ℝ → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hFeven : Function.Even F) (hGeven : Function.Even G)
    (hFgrowth : HasLinearGrowth F) (hGgrowth : HasLinearGrowth G)
    (hFG : MonotoneOn (fun u => G u - F u) (Ici 0)) :
    MonotoneOn (fun z => gaussianOperator ζ v G z - gaussianOperator ζ v F z) (Ici 0) := by
  have hwF (z : ℝ) : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hFgrowth ζ
  have hwG (z : ℝ) : Integrable (fun u => Real.exp (ζ * G u)) (gaussianReal z v) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hG hGgrowth ζ
  have hvp : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hratio := fieldFolded_mass_ratio_monotone v hvp hζ.le F G hFG
    (fun z => fieldFoldedWeight_integrable v hv z ζ F hFeven (hwF z))
    (fun z => fieldFoldedWeight_integrable v hv z ζ G hGeven (hwG z))
    (fun z => fieldFoldedWeight_mass_pos v hv z ζ F hFeven (hwF z))
  intro x hx y hy hxy
  have hr := hratio hx hy hxy
  dsimp only at hr ⊢
  rw [← field_gaussian_exp_ratio_folded v hv ζ F G hFeven hGeven x (hwF x) (hwG x),
    ← field_gaussian_exp_ratio_folded v hv ζ F G hFeven hGeven y (hwF y) (hwG y)] at hr
  have hpF (z : ℝ) := MeasureTheory.integral_exp_pos (hwF z)
  have hpG (z : ℝ) := MeasureTheory.integral_exp_pos (hwG z)
  have hlog := Real.log_le_log (div_pos (hpG x) (hpF x)) hr
  rw [Real.log_div (hpG x).ne' (hpF x).ne', Real.log_div (hpG y).ne' (hpF y).ne'] at hlog
  simpa only [gaussianOperator_eq_gaussian_exp_integral hζ.ne' v hG,
    gaussianOperator_eq_gaussian_exp_integral hζ.ne' v hF, ← mul_sub] using
      mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hζ.le)

/-- Full one-step radial difference preservation, including zero Gaussian
variance and the ordinary root exponent. -/
theorem gaussianOperator_difference_monotone (v : ℝ≥0) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (F G : ℝ → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFeven : Function.Even F) (hGeven : Function.Even G)
    (hFgrowth : HasLinearGrowth F) (hGgrowth : HasLinearGrowth G)
    (hFG : MonotoneOn (fun u => G u - F u) (Ici 0)) :
    MonotoneOn (fun z => gaussianOperator ζ v G z - gaussianOperator ζ v F z) (Ici 0) := by
  by_cases hv : v = 0
  · subst v
    simpa only [NNReal.coe_zero, gaussianOperator_zero_variance] using hFG
  by_cases hz : ζ = 0
  · subst ζ
    exact gaussianOperator_difference_monotone_zero v hv F G hF hG
      hFeven hGeven hFgrowth hGgrowth hFG
  · exact gaussianOperator_difference_monotone_pos v hv (lt_of_le_of_ne hζ (Ne.symm hz))
      F G hF hG hFeven hGeven hFgrowth hGgrowth hFG

end InvariantIsing

end

end OAI
