import OAI.NumberTheory.CubicMoment.Estimates.CubeAsymptotic
import Mathlib.Analysis.SpecialFunctions.PolarCoord

namespace OAI

/-! The three-to-one cubing Jacobian in the radial integral. -/

noncomputable section
open scoped BigOperators
open MeasureTheory MeasureTheory.Measure Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma complex_radial_integral (φ : ℝ → ℂ) :
    (∫ z : ℂ, φ ‖z‖) = (2*Real.pi:ℂ)*(∫ r in Ioi (0:ℝ), (r:ℂ)*φ r) := by
  calc
    _ = ∫ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, (p.1:ℂ)*φ |p.1| := by
      rw [← Complex.integral_comp_polarCoord_symm,polarCoord_target]
      simp only [Complex.norm_polarCoord_symm,Complex.real_smul]
    _ = (∫ r in Ioi (0:ℝ), (r:ℂ)*φ |r|)*(∫ _ in Ioo (-Real.pi) Real.pi, (1:ℂ)) := by
      rw [← setIntegral_prod_mul,volume_eq_prod]
      simp only [mul_one]
    _ = (2*Real.pi:ℂ)*(∫ r in Ioi (0:ℝ), (r:ℂ)*φ r) := by
      have hφ : (∫ r in Ioi (0:ℝ), (r:ℂ)*φ |r|) = ∫ r in Ioi (0:ℝ), (r:ℂ)*φ r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        change (r:ℂ)*φ |r| = (r:ℂ)*φ r
        rw [abs_of_pos hr]
      rw [hφ]
      simp only [integral_const,measureReal_restrict_apply MeasurableSet.univ,
        Set.univ_inter,Complex.real_smul,mul_one]
      rw [Real.volume_real_Ioo_of_le (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos])]
      push_cast
      ring

lemma radial_cubing_integral (φ : ℝ → ℂ) :
    (∫ z : ℂ, φ (‖z‖^3)) = (1/3:ℂ)*
      (∫ z : ℂ, ((‖z‖^(-(4/3:ℝ)):ℝ):ℂ)*φ ‖z‖) := by
  rw [complex_radial_integral (fun r => φ (r^3)),
    complex_radial_integral (fun r => ((r^(-(4/3:ℝ)):ℝ):ℂ)*φ r)]
  have hsub := integral_comp_rpow_Ioi (fun r : ℝ => ((r^(-(1/3:ℝ)):ℝ):ℂ)*φ r)
    (show (3:ℝ) ≠ 0 by norm_num)
  have hp (r : ℝ) (hr : r ∈ Ioi (0:ℝ)) :
      (abs (3:ℝ)*r^((3:ℝ)-1)) • (((((r^(3:ℝ))^(-(1/3:ℝ))):ℝ):ℂ)*φ (r^(3:ℝ))) =
        (3:ℂ)*((r:ℂ)*φ (r^3)) := by
    have hrr : (r^(3:ℝ))^(-(1/3:ℝ)) = r⁻¹ := by
      rw [← Real.rpow_mul hr.le]
      norm_num [Real.rpow_neg_one]
    rw [hrr,Real.rpow_ofNat]
    norm_num
    have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    field_simp
  have hsub' : (3:ℂ)*(∫ r in Ioi (0:ℝ), (r:ℂ)*φ (r^3)) =
      ∫ r in Ioi (0:ℝ), ((r^(-(1/3:ℝ)):ℝ):ℂ)*φ r := by
    rw [← integral_const_mul]
    rw [← hsub]
    exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => (hp r hr).symm)
  have hweight : (∫ r in Ioi (0:ℝ), (r:ℂ)*(((r^(-(4/3:ℝ)):ℝ):ℂ)*φ r)) =
      ∫ r in Ioi (0:ℝ), ((r^(-(1/3:ℝ)):ℝ):ℂ)*φ r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have he : r*r^(-(4/3:ℝ)) = r^(-(1/3:ℝ)) := by
      nth_rw 1 [← Real.rpow_one r]
      rw [← Real.rpow_add hr]
      norm_num
    dsimp only
    rw [← mul_assoc,← Complex.ofReal_mul,he]
  rw [hweight,← hsub']
  ring

end CubicFirstMoment

end

end OAI
