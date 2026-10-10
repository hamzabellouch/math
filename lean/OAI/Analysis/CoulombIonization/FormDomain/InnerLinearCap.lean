import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.InnerCapStatistic

namespace OAI

open MeasureTheory Set Filter
noncomputable section
namespace CoulombAtom
lemma actual_inner_linear_statistic {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) {Z lam h a : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    (hh : 0 < h) (ha : h ≤ a) {y : Space} (hy : 2*a ≤ ‖y‖) :
    sourceField Z (actualInnerSource psi h) y*formMass psi ≤
      (h/a)*Real.sqrt (innerCapStatistic psi Z lam h)*Real.sqrt (formMass psi) := by
  have hap : 0 < a := hh.trans_le ha
  have hm := formMass_nonneg psi
  by_cases hm0 : formMass psi = 0
  · simp only [hm0,mul_zero,Real.sqrt_zero,le_refl]
  have hcap := actual_inner_exterior_cap hpsi hm0 hZ hlam hh (by linarith)
  have hc := actualInnerBoundaryCap_nonneg psi Z hlam hh
  have h1 : sourceField Z (actualInnerSource psi h) y ≤ actualInnerBoundaryCap psi Z lam h*(h/a) := by
    calc
      _ ≤ actualInnerBoundaryCap psi Z lam h*(2*h/‖y‖) := by simpa only [mul_div_assoc] using hcap
      _ ≤ actualInnerBoundaryCap psi Z lam h*(2*h/(2*a)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity) hy) hc
      _ = _ := by congr 1; field_simp
  have hsq := actualInnerBoundaryCap_sq_le_statistic hpsi hZ hlam hh
  have hstat := innerCapStatistic_nonneg psi Z lam h
  have hroot : actualInnerBoundaryCap psi Z lam h*Real.sqrt (formMass psi) ≤
      Real.sqrt (innerCapStatistic psi Z lam h) := by
    apply (sq_le_sq₀ (mul_nonneg hc (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp
    simpa only [mul_pow,Real.sq_sqrt hm,Real.sq_sqrt hstat] using hsq
  have h2 := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg (formMass psi))
  rw [mul_assoc,←sq,Real.sq_sqrt hm] at h2
  calc
    _ ≤ actualInnerBoundaryCap psi Z lam h*(h/a)*formMass psi := mul_le_mul_of_nonneg_right h1 hm
    _ = (h/a)*(actualInnerBoundaryCap psi Z lam h*formMass psi) := by ring
    _ ≤ (h/a)*(Real.sqrt (innerCapStatistic psi Z lam h)*Real.sqrt (formMass psi)) :=
      mul_le_mul_of_nonneg_left h2 (div_nonneg hh.le hap.le)
    _ = _ := by ring
end CoulombAtom

end

end OAI
