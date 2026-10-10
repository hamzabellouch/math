import Mathlib
import OAI.Geometry.Cannon.Conformal.OpenMapMaxSphere
import OAI.Geometry.Cannon.Beltrami.CauchySymbol

namespace OAI

section
section
section
section
section
section
section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
noncomputable section
noncomputable section
noncomputable section
open Set Metric MeasureTheory Filter Complex
open scoped Topology

noncomputable section
noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

namespace CannonMetricQC
open CannonBeltrami MeasureTheory Set Metric

lemma weakQS_partials_locallyIntegrable (f : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hf : WeakQS f H) :
    LocallyIntegrable (partialZ f) volume ∧ LocallyIntegrable (partialBar f) volume := by
  have h1 := (weakQS_full_weakW12 f hH hf 1).1
  have hI := (weakQS_full_weakW12 f hH hf Complex.I).1
  constructor
  · change LocallyIntegrable (fun z => (fderiv ℝ (f : ℂ → ℂ) z 1-Complex.I*fderiv ℝ (f : ℂ → ℂ) z Complex.I)/2) volume
    simpa only [Pi.smul_def,Pi.sub_def,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
      using (h1.sub (hI.smul Complex.I)).smul ((2:ℂ)⁻¹)
  · change LocallyIntegrable (fun z => (fderiv ℝ (f : ℂ → ℂ) z 1+Complex.I*fderiv ℝ (f : ℂ → ℂ) z Complex.I)/2) volume
    simpa only [Pi.smul_def,Pi.add_def,Pi.smul_apply,Pi.add_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
      using (h1.add (hI.smul Complex.I)).smul ((2:ℂ)⁻¹)

lemma weakQS_partial_integration_by_parts (F : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hF : WeakQS F H)
    (φ : SchwartzMap ℂ ℂ) (hc : HasCompactSupport (φ : ℂ → ℂ)) :
    (∫ z, F z*partialZ φ z)=-(∫ z, partialZ F z*φ z) ∧
    (∫ z, F z*partialBar φ z)=-(∫ z, partialBar F z*φ z) := by
  have hfx (v : ℂ) : Integrable (fun z => F z*fderiv ℝ (φ : ℂ → ℂ) z v) :=
    (F.continuous.mul ((φ.smooth'.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hdx (v : ℂ) : Integrable (fun z => fderiv ℝ (F : ℂ → ℂ) z v*φ z) := by
    simpa only [smul_eq_mul] using ((weakQS_full_weakW12 F hH hF v).1).integrable_smul_right_of_hasCompactSupport φ.continuous hc
  have hid (v : ℂ) : (∫ z, F z*fderiv ℝ (φ : ℂ → ℂ) z v)=
      -(∫ z, fderiv ℝ (F : ℂ → ℂ) z v*φ z) := by
    have hh := (weakQS_full_weakW12 F hH hF v).2.2 φ hc
    simpa only [mul_comm,neg_neg] using (congrArg Neg.neg hh).symm
  have h1 := hid 1
  have hI := hid Complex.I
  have hz1 : (fun z => F z*partialZ φ z)=
      (fun z => (F z*fderiv ℝ (φ : ℂ → ℂ) z 1-Complex.I*(F z*fderiv ℝ (φ : ℂ → ℂ) z Complex.I))/2) := by
    ext z; unfold partialZ; ring
  have hz2 : (fun z => partialZ F z*φ z)=
      (fun z => (fderiv ℝ F z 1*φ z-Complex.I*(fderiv ℝ F z Complex.I*φ z))/2) := by
    ext z; unfold partialZ; ring
  have hb1 : (fun z => F z*partialBar φ z)=
      (fun z => (F z*fderiv ℝ (φ : ℂ → ℂ) z 1+Complex.I*(F z*fderiv ℝ (φ : ℂ → ℂ) z Complex.I))/2) := by
    ext z; unfold partialBar; ring
  have hb2 : (fun z => partialBar F z*φ z)=
      (fun z => (fderiv ℝ F z 1*φ z+Complex.I*(fderiv ℝ F z Complex.I*φ z))/2) := by
    ext z; unfold partialBar; ring
  rw [hz1,hz2,hb1,hb2]
  simp only [integral_div,integral_sub (hfx 1) ((hfx Complex.I).const_mul _),
    integral_sub (hdx 1) ((hdx Complex.I).const_mul _),
    integral_add (hfx 1) ((hfx Complex.I).const_mul _),
    integral_add (hdx 1) ((hdx Complex.I).const_mul _),integral_const_mul,h1,hI]
  constructor <;> ring

end CannonMetricQC

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
