import OAI.Geometry.RCD.Heat.NonnegativeKernelBridgeMass
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace OAI

/-! # Exact normalization of an intermediate kernel bridge

The composed kernel and one endpoint marginal fix the intermediate mass.
This is the normalization identity for the entropic interpolation.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {A B Z : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]
  (μ : Measure A) (ν : Measure B) (σ : Measure Z)
  [IsProbabilityMeasure μ] [SFinite ν] [SFinite σ]

theorem kernel_bridge_normalized {F : A → ℝ≥0∞} {G : B → ℝ≥0∞}
    {L : A × Z → ℝ≥0∞} {R : Z × B → ℝ≥0∞} {K : A × B → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) (hL : Measurable L) (hR : Measurable R)
    (hconv : ∀ a b, (∫⁻ z, L (a,z)*R (z,b) ∂σ)=K (a,b))
    (hrow : ∀ a, F a*(∫⁻ b, K (a,b)*G b ∂ν)=1) :
    (∫⁻ z, (∫⁻ a, F a*L (a,z) ∂μ)*(∫⁻ b, R (z,b)*G b ∂ν) ∂σ)=1 := by
  rw [nonnegative_kernel_bridge_mass μ ν σ
    (L := fun z => F z.1 * L z) (R := fun z => R z * G z.2)
    ((hF.comp measurable_fst).mul hL) (hR.mul (hG.comp measurable_snd))]
  have hinner (a : A) (b : B) :
      (∫⁻ z, (F a*L (a,z))*(R (z,b)*G b) ∂σ)=F a*(K (a,b)*G b) := by
    have he : (fun z => (F a*L (a,z))*(R (z,b)*G b)) =
        fun z => F a*((L (a,z)*R (z,b))*G b) := by
      funext z
      ac_rfl
    rw [he,lintegral_const_mul (F a) (f := fun z => (L (a,z)*R (z,b))*G b)
      (((hL.comp (measurable_const.prodMk measurable_id)).mul
      (hR.comp (measurable_id.prodMk measurable_const))).mul_const (G b)),
      lintegral_mul_const (G b) (f := fun z => L (a,z)*R (z,b))
        ((hL.comp (measurable_const.prodMk measurable_id)).mul
        (hR.comp (measurable_id.prodMk measurable_const))),hconv]
  simp_rw [hinner]
  have hKrow (a : A) : Measurable (fun b => K (a,b)) := by
    have hm : Measurable (fun z : B × Z => L (a,z.2)*R (z.2,z.1)) :=
      (hL.comp (measurable_const.prodMk measurable_snd)).mul
        (hR.comp (measurable_snd.prodMk measurable_fst))
    have hh : Measurable (fun b => ∫⁻ z, L (a,z)*R (z,b) ∂σ) := hm.lintegral_prod_right'
    simpa only [hconv] using hh
  have hout (a : A) : (∫⁻ b, F a*(K (a,b)*G b) ∂ν)=1 := by
    rw [lintegral_const_mul (F a) (f := fun b => K (a,b)*G b) ((hKrow a).mul hG),hrow]
  simp_rw [hout]
  simp

theorem kernel_bridge_probability {F : A → ℝ≥0∞} {G : B → ℝ≥0∞}
    {L : A × Z → ℝ≥0∞} {R : Z × B → ℝ≥0∞} {K : A × B → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) (hL : Measurable L) (hR : Measurable R)
    (hconv : ∀ a b, (∫⁻ z, L (a,z)*R (z,b) ∂σ)=K (a,b))
    (hrow : ∀ a, F a*(∫⁻ b, K (a,b)*G b ∂ν)=1) :
    IsProbabilityMeasure (σ.withDensity
      (fun z => (∫⁻ a, F a*L (a,z) ∂μ)*(∫⁻ b, R (z,b)*G b ∂ν))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact kernel_bridge_normalized μ ν σ hF hG hL hR hconv hrow

end RegularPointCoordinates

end

end OAI
