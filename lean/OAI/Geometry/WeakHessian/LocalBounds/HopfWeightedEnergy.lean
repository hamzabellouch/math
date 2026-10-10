import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HopfHeatCommutation

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile89
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma finite_densityMeasure (u : Lp ℝ 2 m) (hu : Integrable u m) :
    IsFiniteMeasure (densityMeasure m u) := by
  constructor
  rw [densityMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact (lintegral_mono fun x => Real.ofReal_le_enorm (u x)).trans_lt hu.hasFiniteIntegral

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma heat_integral_bounded_version (h : QuadraticCheegerEnergy m)
    (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (f F : X →ᵇ ℝ) (hf2 : MemLp f 2 m) {t : ℝ} (ht : 0 ≤ t)
    (hF : F =ᵐ[m] cheegerHeat h t (hf2.toLp f)) :
    (∫ x,F x ∂densityMeasure m u) = ∫ x,cheegerHeat h t u x*f x ∂m := by
  rw [← integral_densityMeasure m _ (cheegerHeat_nonneg h ht u hun)]
  calc
    (∫ x,F x ∂densityMeasure m u) = (∫ x,cheegerHeat h t (hf2.toLp f) x ∂densityMeasure m u) :=
      integral_congr_ae ((densityMeasure_ac m u).ae_le hF)
    _ = ⟪cheegerHeat h t (hf2.toLp f),u⟫_ℝ := integral_densityMeasure_L2 _ _ hun
    _ = ∫ x,hf2.toLp f x ∂densityMeasure m (cheegerHeat h t u) :=
      (cheegerHeat_density_duality h u _ ht hun).symm
    _ = ∫ x,f x ∂densityMeasure m (cheegerHeat h t u) :=
      integral_congr_ae ((densityMeasure_ac m _).ae_le hf2.coeFn_toLp)

lemma RCD.hopf_heat_integral_commutation {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (f F : X →ᵇ ℝ)
    (hf : GloballyLipschitz (f : X → ℝ)) (hfc : HasCompactSupport (f : X → ℝ))
    (hf2 : MemLp f 2 m) {t : ℝ} (ht : 0 ≤ t)
    (hF : F =ᵐ[m] cheegerHeat h t (hf2.toLp f))
    (u : Lp ℝ 2 m) (hu : Integrable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {s : ℝ} (hs : 0 < s) :
    (∫ x,F x-boundedHopfMap F (s*Real.exp (2*K*t)) x ∂densityMeasure m u) ≤
      ∫ x,cheegerHeat h t u x*(f x-boundedHopfMap f s x) ∂m := by
  let : IsFiniteMeasure (densityMeasure m u) := finite_densityMeasure u hu
  let : Measure.IsOpenPosMeasure m := hfull.openPosMeasure
  have hQ2 := boundedHopfMap_memLp_compact hfin f o hfc hs
  obtain ⟨F',Q,hFl,hQl,hFe,hQe,hFb,hcomm⟩ :=
    hrcd.hopf_heat_commutation hN hfull hfin h f hf hf2 hs hQ2 ht
  have he : F' = F := BoundedContinuousFunction.ext fun x => congrFun (Measure.eq_of_ae_eq (hFe.trans hF.symm) F'.continuous F.continuous) x
  subst F'
  have hPu := (hrcd.1.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hu ht).1
  have H := integral_mono_ae ((F-boundedHopfMap F (s*Real.exp (2*K*t))).integrable (μ := densityMeasure m u))
    ((F-Q).integrable (μ := densityMeasure m u)) (ae_of_all _ fun x => by
      simp only [BoundedContinuousFunction.sub_apply,boundedHopfMap_apply_pos F (mul_pos hs (Real.exp_pos _))]
      linarith [hcomm x])
  simp only [BoundedContinuousFunction.sub_apply] at H
  rw [integral_sub (F.integrable (μ := densityMeasure m u)) (Q.integrable (μ := densityMeasure m u)),
    heat_integral_bounded_version h u hun f F hf2 ht hF,
    heat_integral_bounded_version h u hun _ Q hQ2 ht hQe] at H
  have hsub : (∫ x,cheegerHeat h t u x*(f x-boundedHopfMap f s x) ∂m) =
      (∫ x,cheegerHeat h t u x*f x ∂m)-(∫ x,cheegerHeat h t u x*boundedHopfMap f s x ∂m) := by
    simp_rw [mul_sub]
    exact integral_sub (integrable_bounded_pairing hPu f) (integrable_bounded_pairing hPu _)
  rwa [hsub]
end WeakHessian

end
end InlinedFile89

end OAI
