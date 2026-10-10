import Mathlib
import OAI.Analysis.Conductivity.Fourier.AngularNormalTrace

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma continuous_sourceAngular (t : ℝ) :
    Continuous (fun z : ℝ×UnitAddTorus (Fin 2) => sourceAngularCollar (t+z.1) z.2) := by
  simp_rw [sourceAngular_affine]
  exact ((continuous_sourceAngularCollar t).comp continuous_snd).add
    (continuous_fst.smul (continuous_sourceAngularVelocity.comp continuous_snd))

lemma continuous_parametric_interval {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X] {f : X → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) {a b : ℝ} (hab : a≤b) :
    Continuous (fun x => ∫ t in a..b,f x t) := by
  have hh := continuous_parametric_integral_of_continuous (μ:=volume) hf (s:=Icc a b) isCompact_Icc
  simpa only [intervalIntegral.integral_of_le hab,integral_Icc_eq_integral_Ioc] using hh

lemma continuous_torus_interval_swap {f : ℝ → UnitAddTorus (Fin 2) → ℝ}
    (hf : Continuous (Function.uncurry f)) (a b : ℝ) :
    (∫ t in a..b,∫ x,f t x)=∫ x,∫ t in a..b,f t x := by
  have hi : IntegrableOn (Function.uncurry f) (uIoc a b ×ˢ (univ : Set (UnitAddTorus (Fin 2)))) :=
    (hf.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_univ)).mono_set
      (prod_mono uIoc_subset_uIcc Subset.rfl)
  apply intervalIntegral_integral_swap
  simpa only [IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict,Measure.restrict_univ] using hi

def sourcePhysicalEnergy (f : (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) : ℝ :=
  64*‖fderiv ℝ f y‖^2+2*(f y)^2

lemma sourcePhysicalEnergy_nonneg (f : (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) :
    0≤ sourcePhysicalEnergy f y := by unfold sourcePhysicalEnergy; positivity

lemma continuous_sourcePhysicalEnergy {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) : Continuous (sourcePhysicalEnergy f) :=
  (continuous_const.mul ((hf.continuous_fderiv (by simp)).norm.pow 2)).add
    (continuous_const.mul (hf.continuous.pow 2))

lemma integrate_torus_interval_bound {F : UnitAddTorus (Fin 2) → ℝ}
    {G : ℝ → UnitAddTorus (Fin 2) → ℝ} (hF : Continuous F)
    (hG : Continuous (Function.uncurry G)) {a b C : ℝ} (hab : a≤b)
    (hb : ∀ x,F x≤C*(∫ t in a..b,G t x)) :
    (∫ x,F x)≤C*(∫ t in a..b,∫ x,G t x) := by
  have hs : Continuous (Function.uncurry (fun x t => G t x)) := hG.comp continuous_swap
  have ht : Continuous (fun x => ∫ t in a..b,G t x) := continuous_parametric_interval hs hab
  have hi : Integrable (fun x => C*(∫ t in a..b,G t x)) :=
    (continuous_const.mul ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [continuous_torus_interval_swap hG,←integral_const_mul]
  exact integral_mono (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hi hb

theorem sourceAngular_integrated_trace {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (t : ℝ) {η : ℝ} (hη : 0<η) :
    (∫ x : UnitAddTorus (Fin 2),(f (sourceAngularCollar t x))^2)≤
      (1+1/η)*(∫ a in (0:ℝ)..η,∫ x : UnitAddTorus (Fin 2),
        sourcePhysicalEnergy f (sourceAngularCollar (t+a) x)) := by
  apply integrate_torus_interval_bound (F:=fun x => (f (sourceAngularCollar t x))^2)
    (G:=fun a x => sourcePhysicalEnergy f (sourceAngularCollar (t+a) x))
    ((hf.continuous.comp (continuous_sourceAngularCollar t)).pow 2)
    ((continuous_sourcePhysicalEnergy hf).comp (continuous_sourceAngular t)) hη.le
  intro x
  exact sourceAngular_pointwise_trace hf t hη x

end ScalarConductivity

end

end OAI
