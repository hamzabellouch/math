import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.LaplacianCompDilation
import OAI.Analysis.CoulombIonization.FieldAnalysis.BarrierNuclearBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombPDE

lemma tfPotential_dilation {b : ℝ} (hb : 0 < b) (ρ : TFSpace → ℝ) (x : TFSpace) :
    tfPotential (tfDilation b ρ) x = b^4*tfPotential ρ (b • x) := by
  have he (y : TFSpace) : tfDilation b ρ y/‖x-y‖ =
      b^7*(ρ (b • y)/‖b • x-b • y‖) := by
    rw [tfDilation,←smul_sub,norm_smul,Real.norm_of_nonneg hb.le]
    field_simp
  simp only [tfPotential,he,integral_const_mul]
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun y : TFSpace => ρ y/‖b • x-y‖) b (hR := hb.le),space_finrank]
  simp only [smul_eq_mul]
  field_simp

lemma nuclearField_dilation {b : ℝ} (hb : 0 < b) (Z : ℝ) (x : TFSpace) :
    b^4*nuclearField Z (b • x) = nuclearField (b^3*Z) x := by
  simp only [nuclearField,norm_smul,Real.norm_of_nonneg hb.le]
  field_simp

lemma weakNuclearLower_dilation {b Z : ℝ} (hb : 0 < b) {u h : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn univ Z u h) :
    WeakNuclearLowerOn univ (b^3*Z) (fun x => b^4*u (b • x)) (tfDilation b h) := by
  intro φ hφ hc _ hn
  let ψ : TFSpace → ℝ := fun x => φ (b⁻¹ • x)
  have hψ : ContDiff ℝ 2 ψ := hφ.comp (contDiff_id.const_smul b⁻¹)
  have hcψ : HasCompactSupport ψ := hc.comp_smul (inv_ne_zero hb.ne')
  have hi := mul_le_mul_of_nonneg_left
    (hw ψ hψ hcψ (subset_univ _) (fun x => hn _)) (pow_nonneg hb.le 3)
  have heh : (∫ x, tfDilation b h x*φ x) = b^3*(∫ x, h x*ψ x) := by
    have he : (fun x => tfDilation b h x*φ x) =
        fun x => b^6*((fun y => h y*ψ y) (b • x)) := by
      funext x
      simp only [tfDilation,ψ,smul_smul,inv_mul_cancel₀ hb.ne',one_smul]
      ring
    rw [he,integral_const_mul,Measure.integral_comp_smul_of_nonneg volume
      (fun y => h y*ψ y) b (hR := hb.le)]
    rw [show Module.finrank ℝ TFSpace = 3 from space_finrank]
    simp only [smul_eq_mul]
    change b^6*((b^3)⁻¹*(∫ y, h y*ψ y)) = _
    field_simp
  have heu : (∫ x, b^4*u (b • x)*Δ φ x) = b^3*(∫ x, u x*Δ ψ x) := by
    have he : (fun x => u x*Δ ψ x) =
        fun x => (b⁻¹)^2*((fun y => u (b • y)*Δ φ y) (b⁻¹ • x)) := by
      funext x
      rw [show Δ ψ x = (b⁻¹)^2*Δ φ (b⁻¹ • x) from
        laplacian_comp_dilation b⁻¹ x hφ.contDiffAt]
      simp only [smul_smul,mul_inv_cancel₀ hb.ne',one_smul]
      ring
    rw [he,integral_const_mul,Measure.integral_comp_smul_of_nonneg volume
      (fun y => u (b • y)*Δ φ y) b⁻¹ (hR := (inv_pos.mpr hb).le)]
    have hel : (fun x => b^4*u (b • x)*Δ φ x) =
        fun x => b^4*(u (b • x)*Δ φ x) := by funext x; ring
    rw [hel,integral_const_mul]
    rw [show Module.finrank ℝ TFSpace = 3 from space_finrank]
    simp only [smul_eq_mul]
    change b^4*(∫ x, u (b • x)*Δ φ x) =
      b^3*((b⁻¹)^2*(((b⁻¹)^3)⁻¹*(∫ y, u (b • y)*Δ φ y)))
    field_simp
  rw [heh,heu]
  have hz : ψ 0 = φ 0 := by simp [ψ]
  rw [hz] at hi
  calc
    _ = b^3*(-(4*Real.pi*Z)*φ 0+(∫ x, h x*ψ x)) := by ring
    _ ≤ _ := hi

end CoulombBarrier

end

end OAI
