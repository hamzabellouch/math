import OAI.Geometry.RCD.Transport.BoltzmannDisjointAdditivity
import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Entropy bounds on a finite reference region

These are the upper density bound and the lower volume bound used after
normalizing a restricted transport component.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem entropy_density_volume_tangent {V r : ℝ} (hV : 0<V) (hr : 0≤r) :
    r*(1-Real.log V)-V⁻¹ ≤ r*Real.log r := by
  have h := Real.self_sub_one_le_mul_log (mul_nonneg hV.le hr)
  rw [entropy_density_mul hV hr] at h
  apply (mul_le_mul_iff_right₀ hV).mp
  calc
    V*(r*(1-Real.log V)-V⁻¹)=V*r-1-(V*Real.log V)*r := by
      rw [mul_sub,mul_inv_cancel₀ hV.ne']
      ring
    _ ≤ V*(r*Real.log r) := by linarith

variable {X : Type*} [MeasurableSpace X]

theorem boltzmannEntropy_ge_neg_log_mass (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (ha : ν ≪ μ)
    (he : Integrable (fun x => (ν.rnDeriv μ x).toReal * Real.log (ν.rnDeriv μ x).toReal) μ) :
    -Real.log (μ.real univ) ≤ boltzmannEntropy μ ν := by
  have hμ0 : μ univ≠0 := by
    intro hzero
    have h := ha hzero
    exact one_ne_zero (by simpa only [measure_univ] using h)
  have hV : 0<μ.real univ := ENNReal.toReal_pos hμ0 (measure_ne_top _ _)
  have hl : Integrable (fun x => (ν.rnDeriv μ x).toReal*(1-Real.log (μ.real univ))-
      (μ.real univ)⁻¹) μ :=
    (Measure.integrable_toReal_rnDeriv.mul_const _).sub (integrable_const _)
  have h := integral_mono_ae hl he (.of_forall fun x =>
    entropy_density_volume_tangent hV ENNReal.toReal_nonneg)
  rw [integral_sub (Measure.integrable_toReal_rnDeriv.mul_const _) (integrable_const _),
    integral_mul_const,Measure.integral_toReal_rnDeriv ha,integral_const] at h
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_mul,smul_eq_mul] at h ⊢
  rw [mul_inv_cancel₀ (show (μ univ).toReal≠0 from hV.ne')] at h
  change _ ≤ boltzmannEntropy μ ν at h
  linarith

theorem boltzmannEntropy_le_log_density (μ ν : Measure X) [SigmaFinite μ]
    [IsProbabilityMeasure ν] {C : ℝ} (hC : 0<C) (hν : ν≤ENNReal.ofReal C • μ)
    (he : Integrable (fun x => (ν.rnDeriv μ x).toReal * Real.log (ν.rnDeriv μ x).toReal) μ) :
    boltzmannEntropy μ ν ≤ Real.log C := by
  have ha := Measure.absolutelyContinuous_of_le_smul hν
  have hbound := rnDeriv_le_const_of_le_smul μ ν hν
  have hρ : ∀ᵐ x ∂μ, (ν.rnDeriv μ x).toReal≤C := by
    filter_upwards [hbound] with x hx
    exact (ENNReal.toReal_mono (by finiteness) hx).trans_eq (ENNReal.toReal_ofReal hC.le)
  have hh : ∀ᵐ x ∂μ, (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal ≤
      (ν.rnDeriv μ x).toReal*Real.log C := by
    filter_upwards [hρ] with x hx
    rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a:=ν.rnDeriv μ x)) with hz | hz
    · simp only [←hz,zero_mul,le_refl]
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log hz hx) hz.le
  have h := integral_mono_ae he (Measure.integrable_toReal_rnDeriv.mul_const _) hh
  rw [integral_mul_const,Measure.integral_toReal_rnDeriv ha] at h
  simpa only [boltzmannEntropy,Measure.real,measure_univ,ENNReal.toReal_one,one_mul] using h

theorem boltzmannEntropy_ge_neg_log_support (μ ν : Measure X) [SigmaFinite μ]
    [IsProbabilityMeasure ν] {B : Set X} (hB : MeasurableSet B)
    [IsFiniteMeasure (μ.restrict B)] (ha : ν ≪ μ.restrict B)
    (he : Integrable (fun x => (ν.rnDeriv μ x).toReal * Real.log (ν.rnDeriv μ x).toReal) μ) :
    -Real.log (μ.real B) ≤ boltzmannEntropy μ ν := by
  rw [boltzmannEntropy_localized μ ν hB ha]
  simpa only [Measure.real,Measure.restrict_apply_univ] using
    boltzmannEntropy_ge_neg_log_mass (μ.restrict B) ν ha
      ((entropy_integrable_localized_iff μ ν hB ha).mp he)

end RegularPointCoordinates

end

end OAI
