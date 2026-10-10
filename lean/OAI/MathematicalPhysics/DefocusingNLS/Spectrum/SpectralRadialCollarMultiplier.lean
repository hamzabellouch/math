import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialCollarMeasure
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialCoreTrace
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralL2ComplexMultiplier

namespace OAI

/-! The derivative of a collar cutoff is controlled by the local derivative energy. -/

open Set MeasureTheory Filter
namespace DefocusingNLS

theorem spectralRadialCollarMultiplier_bound (R l U : ℝ) (hR : 0 < R)
    (hl : 0 < l) (hlU : l ≤ U) (hUR : U ≤ R) (d : ℝ → ℝ)
    (hd : AEStronglyMeasurable d (radialPressureMeasure R)) (M : ℝ)
    (hM : ∀ᵐ r ∂radialPressureMeasure R, ‖d r‖ ≤ M)
    (hs : ∀ r ∉ Icc l U, d r=0) (u : SpectralRadialEnergy R)
    (hu : spectralRadialPointValue R hR l hl u=0) :
    ‖spectralL2ComplexMultiplier (radialPressureMeasure R) d hd M hM (spectralRadialValue R u)‖^2 ≤
      M^2*(U-l)^2*R^11*(l^11)⁻¹*
        ‖spectralRadialIntervalMask R l U (spectralRadialDerivative R u)‖^2 := by
  let v := spectralL2ComplexMultiplier (radialPressureMeasure R) d hd M hM (spectralRadialValue R u)
  let E := ‖spectralRadialIntervalMask R l U (spectralRadialDerivative R u)‖^2
  let B := M^2*(U-l)*(l^11)⁻¹*E
  have hB : 0 ≤ B := by dsimp [B,E]; positivity
  have hlocal (r : ℝ) (hr : r ∈ Icc l U) :
      ‖spectralRadialPointValue R hR r (hl.trans_le hr.1) u‖^2 ≤ (U-l)*(l^11)⁻¹*E := by
    have hi := spectralRadialPointValue_local_increment R l r U hR hl hr.1 hr.2 hUR u
    rw [hu,sub_zero] at hi
    exact hi.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (sub_le_sub_right hr.2 l) (inv_nonneg.mpr (pow_nonneg hl.le 11)))
      (sq_nonneg _))
  have hp : ∀ᵐ r ∂radialPressureMeasure R,
      ‖v r‖^2 ≤ (Icc l U).indicator (fun _ => B) r := by
    filter_upwards [spectralL2ComplexMultiplier_ae (radialPressureMeasure R) d hd M hM
        (spectralRadialValue R u),spectralRadialRepresentative_ae R hR u,hM]
        with r hv hr hdM
    rw [show v r=d r • spectralRadialValue R u r from hv]
    by_cases hm : r ∈ Icc l U
    · rw [indicator_of_mem hm,← hr,spectralRadialRepresentative,dite_eq_left (hl.trans_le hm.1),
        norm_smul,mul_pow]
      calc
        _ ≤ M^2*((U-l)*(l^11)⁻¹*E) := mul_le_mul
          (pow_le_pow_left₀ (norm_nonneg _) hdM 2) (hlocal r hm) (sq_nonneg _) (sq_nonneg _)
        _ = B := by dsimp [B]; ring
    · simp only [hs r hm,zero_smul,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),
        indicator_of_notMem hm,le_refl]
  have hvint : Integrable (fun r => ‖v r‖^2) (radialPressureMeasure R) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hbi : Integrable ((Icc l U).indicator (fun _ : ℝ => B)) (radialPressureMeasure R) :=
    (integrable_const B).indicator measurableSet_Icc
  have hn : ‖v‖^2=∫ r, ‖v r‖^2 ∂radialPressureMeasure R := by
    rw [← real_inner_self_eq_norm_sq]
    change (∫ r, inner ℝ (v r) (v r) ∂radialPressureMeasure R)=_
    simp only [real_inner_self_eq_norm_sq]
  calc
    ‖v‖^2 = _ := hn
    _ ≤ ∫ r, (Icc l U).indicator (fun _ : ℝ => B) r ∂radialPressureMeasure R :=
      integral_mono_ae hvint hbi hp
    _ = B*(∫ _ in Icc l U, (1 : ℝ) ∂radialPressureMeasure R) := by
      rw [integral_indicator measurableSet_Icc,← integral_const_mul]
      simp only [mul_one]
    _ ≤ B*((U-l)*R^11) := mul_le_mul_of_nonneg_left
      (spectralRadialMeasure_collar_bound R l U hl.le hlU hUR) hB
    _ = _ := by dsimp [B,E]; ring

end DefocusingNLS

end OAI
