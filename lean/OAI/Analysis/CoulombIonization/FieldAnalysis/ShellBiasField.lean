import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.ShellMeanStatistic
import OAI.Analysis.CoulombIonization.RadialBounds.ShellBiasEnergy

namespace OAI

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
noncomputable section
namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply FermionLipschitzMultiplier.apply oneBodySquareTotal
  formEnergy energy sectorExcessOperator fermionGraphValue shellBiasMultiplier

lemma shellInnerField_le_closed {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z : ℝ) {h H : ℝ} (hh : h < H) (x : Configuration N) :
    oneBodyInnerField p Z H x ≤ closedShellField p Z h x := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (rawInnerField_le_closed hh Z x (x i)) (sq_nonneg _)

lemma closedShellField_density_integrable {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z : ℝ) {h a : ℝ} (ha : 0 < a) (hh : h ≤ a)
    (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖) (F : fermionGraph N) (s : Spins N) :
    Integrable (fun x => closedShellField p Z h x*‖graphComponent s none F x‖^2) := by
  obtain ⟨B,hB⟩ := (oneBodySquareTotal (N := N) p).bound
  have hC : 0 ≤ |Z|/(2*a)+(N:ℝ)/a := by positivity
  have hb (x : Configuration N) : ‖closedShellField p Z h x‖ ≤ (|Z|/(2*a)+(N:ℝ)/a)*B := by
    rw [Real.norm_eq_abs]
    exact (closedShellField_bound p Z ha hh hp x).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hB x)) hC)
  exact (Lp.memLp (graphComponent s none F)).norm.integrable_sq.bdd_mul
    (closedShellField_measurable N p Z h).aestronglyMeasurable (ae_of_all _ hb)

lemma shellInnerIntegral_le_biasPair {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (Z : ℝ) {h H a : ℝ} (ha : 0 < a) (hh : h ≤ a)
    (hH : h < H) (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖) (F : fermionGraph N) :
    (∫ x, oneBodyInnerField p Z H x ∂formRawLaw (graphFormVector F)) ≤
      rawFormPair (graphFormVector ((shellBiasMultiplier p hc).apply F)) (shellMeanField p Z h) := by
  rw [rawFormPair_shellBias p hc F]
  have he (x : Configuration N) : shellMeanField p Z h x*(oneBodySquareTotal p).value x = closedShellField p Z h x := by
    rw [mul_comm,oneBodySquareTotal_mul_shellMeanField]
  simp_rw [he]
  rw [formRawLaw_integral (graphFormVector_sobolev F).sobolevVector]
  simp only [formRawDensity,graphFormVector_value_eq,Finset.sum_mul]
  simp_rw [mul_comm (‖graphComponent _ none F _‖^2)]
  rw [integral_finsetSum _ (fun s _ => oneBodyInnerField_density_integrable p Z H F s)]
  unfold rawFormPair
  simp only [graphFormVector_value_eq]
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono (oneBodyInnerField_density_integrable p Z H F s)
    (closedShellField_density_integrable p Z ha hh hp F s)
  intro x
  exact mul_le_mul_of_nonneg_right (shellInnerField_le_closed p Z hH x) (sq_nonneg _)

lemma shellBias_normalized_excess {Z lam D : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (F : fermionGraph N)
    (p : SmoothMultiplier spaceDirections) (hc : HasCompactSupport p.value)
    (hm : 0 < formMass (graphFormVector ((shellBiasMultiplier p hc).apply F)))
    (he : corePriceExcess Z lam (graphFormVector ((shellBiasMultiplier p hc).apply F)) ≤
      D*formMass (graphFormVector ((shellBiasMultiplier p hc).apply F))) :
    max (corePriceExcess Z lam (scaleForm (Real.sqrt (formMass
      (graphFormVector ((shellBiasMultiplier p hc).apply F))))⁻¹
        (graphFormVector ((shellBiasMultiplier p hc).apply F)))) 0 ≤ D := by
  let psi := graphFormVector ((shellBiasMultiplier p hc).apply F)
  have hn := corePriceExcess_nonneg (graphFormVector_sobolev ((shellBiasMultiplier p hc).apply F)) hZ hlam
  have hD : 0 ≤ D := nonneg_of_mul_nonneg_left (hn.trans he) hm
  apply max_le _ hD
  rw [corePriceExcess_scale,inv_pow,Real.sq_sqrt hm.le]
  have hi := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hm.le)
  calc
    _ ≤ (formMass psi)⁻¹*(D*formMass psi) := hi
    _ = D := by rw [mul_comm D (formMass psi),←mul_assoc,inv_mul_cancel₀ (show formMass psi ≠ 0 from hm.ne'),one_mul]

end CoulombAtom

end

end OAI
