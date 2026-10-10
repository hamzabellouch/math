import OAI.Probability.InvariantIsing.Fields.FieldFoldedDensity
import Mathlib.MeasureTheory.Group.Integral

namespace OAI

/-! Gaussian integral form of the folded one-site transition. -/

noncomputable section
open scoped NNReal
open MeasureTheory ProbabilityTheory Set

namespace InvariantIsing

lemma field_integral_fold (g : ℝ → ℝ) (hg : Integrable g volume) :
    (∫ x, g x) = ∫ u in Ici (0 : ℝ), g u + g (-u) := by
  have he : (fun u => (Iic (0 : ℝ)).indicator g (-u)) =
      (Ici (0 : ℝ)).indicator (fun u => g (-u)) := by
    funext u
    simp only [Set.indicator, mem_Iic, mem_Ici, neg_nonpos]
  have hn := integral_neg_eq_self ((Iic (0 : ℝ)).indicator g) volume
  rw [he, integral_indicator measurableSet_Ici, integral_indicator measurableSet_Iic] at hn
  rw [integral_add hg.integrableOn hg.comp_neg.integrableOn, hn, integral_Ici_eq_integral_Ioi]
  calc
    (∫ x, g x) = (∫ x in Iic 0, g x) + ∫ x in Ioi 0, g x := by
      simpa only [compl_Iic] using (integral_add_compl (s := Iic 0) measurableSet_Iic hg).symm
    _ = _ := add_comm _ _

lemma field_gaussian_density_integrable (v : ℝ≥0) (hv : v ≠ 0) (z : ℝ)
    (f : ℝ → ℝ) (hf : Integrable f (gaussianReal z v)) :
    Integrable (fun u => gaussianPDFReal z v u * f u) volume := by
  rw [gaussianReal_of_var_ne_zero z hv] at hf
  have he := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF z v) (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))).mp hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using he

/-- Folding a Gaussian with an even terminal tilt gives precisely the
positive-half-line density used in the likelihood-ratio comparison. -/
theorem field_gaussian_folded_integral (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F f : ℝ → ℝ) (hF : Function.Even F)
    (hf : Integrable (fun u => Real.exp (ζ * F u) * f |u|) (gaussianReal z v)) :
    (∫ u, Real.exp (ζ * F u) * f |u| ∂gaussianReal z v) =
      (2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * v))) *
        ∫ u in Ici (0 : ℝ), f u * fieldFoldedWeight v ζ F z u := by
  let C := 2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * (v : ℝ)))
  let g := fun u => gaussianPDFReal z v u * (Real.exp (ζ * F u) * f |u|)
  have hg : Integrable g volume := field_gaussian_density_integrable v hv z _ hf
  rw [integral_gaussianReal_eq_integral_smul hv]
  change (∫ u, g u) = _
  rw [field_integral_fold g hg, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ici
  intro u hu
  dsimp only [g]
  rw [abs_of_nonneg hu, abs_neg, abs_of_nonneg hu, hF u]
  have he := field_gaussian_pair_sum v hv z u
  change _ = C * (f u * fieldFoldedWeight v ζ F z u)
  calc
    _ = (gaussianPDFReal z v u + gaussianPDFReal z v (-u)) *
        (Real.exp (ζ * F u) * f u) := by ring
    _ = _ := by rw [he]; dsimp only [fieldFoldedWeight, C]; ring

lemma field_folded_constant_pos (v : ℝ≥0) (hv : v ≠ 0) (z : ℝ) :
    0 < 2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * v)) := by
  have hvp : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  positivity

/-- Gaussian exponential integrability supplies the folded density's
integrability; no separate density-tail assumption is needed. -/
lemma fieldFoldedWeight_integrable (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F : ℝ → ℝ) (hF : Function.Even F)
    (hweight : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v)) :
    Integrable (fieldFoldedWeight v ζ F z) (volume.restrict (Ici 0)) := by
  let C := 2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * (v : ℝ)))
  let g := fun u => gaussianPDFReal z v u * Real.exp (ζ * F u)
  have hg : Integrable g volume := field_gaussian_density_integrable v hv z _ hweight
  have hi : Integrable (fun u => g u + g (-u)) (volume.restrict (Ici 0)) :=
    hg.integrableOn.add hg.comp_neg.integrableOn
  have he : (fun u => g u + g (-u)) =ᵐ[volume.restrict (Ici 0)]
      (fun u => C * fieldFoldedWeight v ζ F z u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u _hu
    dsimp only [g]
    rw [hF u]
    have hp := field_gaussian_pair_sum v hv z u
    calc
      _ = (gaussianPDFReal z v u + gaussianPDFReal z v (-u)) * Real.exp (ζ * F u) := by ring
      _ = _ := by rw [hp]; dsimp only [C, fieldFoldedWeight]; ring
  have hc : C ≠ 0 := (field_folded_constant_pos v hv z).ne'
  have hi' := (hi.congr he).const_mul C⁻¹
  simpa only [Pi.mul_apply, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hi'

lemma fieldFoldedWeight_mass_pos (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F : ℝ → ℝ) (hF : Function.Even F)
    (hweight : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v)) :
    0 < ∫ u in Ici (0 : ℝ), fieldFoldedWeight v ζ F z u := by
  have hi := fieldFoldedWeight_integrable v hv z ζ F hF hweight
  apply (integral_pos_iff_support_of_nonneg (fun u => (fieldFoldedWeight_pos v ζ F z u).le) hi).mpr
  have he : Function.support (fieldFoldedWeight v ζ F z) = univ := by
    ext u
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (fieldFoldedWeight_pos v ζ F z u).ne'
  rw [he, Measure.restrict_apply_univ]
  simp

lemma field_gaussian_folded_ratio (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F f : ℝ → ℝ) (hF : Function.Even F)
    (hf : Integrable (fun u => Real.exp (ζ * F u) * f |u|) (gaussianReal z v))
    (hweight : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v)) :
    (∫ u, Real.exp (ζ * F u) * f |u| ∂gaussianReal z v) /
        (∫ u, Real.exp (ζ * F u) ∂gaussianReal z v) =
      (∫ u in Ici (0 : ℝ), f u * fieldFoldedWeight v ζ F z u) /
        (∫ u in Ici (0 : ℝ), fieldFoldedWeight v ζ F z u) := by
  have hn := field_gaussian_folded_integral v hv z ζ F f hF hf
  have hd := field_gaussian_folded_integral v hv z ζ F (fun _ => 1) hF
    (by simpa only [mul_one] using hweight)
  simp only [mul_one, one_mul] at hd
  rw [hn, hd, mul_div_mul_left _ _ (field_folded_constant_pos v hv z).ne']

end InvariantIsing

end

end OAI
