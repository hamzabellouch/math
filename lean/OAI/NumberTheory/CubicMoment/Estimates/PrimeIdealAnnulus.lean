import OAI.NumberTheory.CubicMoment.Estimates.ThinAnnulusCount
import OAI.NumberTheory.CubicMoment.Estimates.IdealLogDirichlet

namespace OAI

/-! The lattice annulus estimate for actual ideals, and its von Mangoldt
weighted form. Injectivity of the canonical generator retains multiplicity. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem idealExponent_annulus_card (S : Finset EisensteinIdealExponent) {A B : ℝ}
    (hA : 1 ≤ A) (hAB : A ≤ B)
    (hS : ∀ ν ∈ S, A ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ B) :
    (S.card:ℝ) ≤ 4*(B-A+Real.sqrt B+Real.sqrt A) := by
  have hc := eisenstein_annulus_card (S.image idealExponentGenerator) hA hAB (by
    intro a ha
    obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp ha
    simpa only [idealExponentNorm, normNat_cast] using hS ν hν)
  rw [Finset.card_image_of_injective _ idealExponentGenerator_injective] at hc
  exact hc

theorem idealMangoldt_annulus_mass (S : Finset EisensteinIdealExponent)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {A B : ℝ}
    (hA : 1 ≤ A) (hAB : A ≤ B)
    (hS : ∀ ν ∈ S, A ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ B) :
    (∑ ν ∈ S, ‖((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν‖) ≤
      4*(B-A+Real.sqrt B+Real.sqrt A)*Real.log B := by
  have hB : 1 ≤ B := hA.trans hAB
  calc
    _ ≤ ∑ _ν ∈ S, Real.log B := by
      apply Finset.sum_le_sum
      intro ν hν
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      calc
        _ ≤ |(MvPowerSeries.coeff ν idealVonMangoldt:ℝ)| :=
          mul_le_of_le_one_right (abs_nonneg _) (hχ ν)
        _ ≤ Real.log (idealExponentNorm ν) := idealVonMangoldt_coeff_abs_le_logNorm ν
        _ ≤ Real.log B := Real.log_le_log (idealExponentNorm_pos ν) (hS ν hν).2
    _ = (S.card:ℝ)*Real.log B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (idealExponent_annulus_card S hA hAB hS)
      (Real.log_nonneg hB)

end CubicFirstMoment

end

end OAI
