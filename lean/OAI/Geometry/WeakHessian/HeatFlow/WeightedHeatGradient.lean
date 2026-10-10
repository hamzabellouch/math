import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.LocalMeasureGradient
import OAI.Geometry.WeakHessian.LocalBounds.HopfWeightedEnergy
import OAI.Geometry.WeakHessian.LocalBounds.HopfEnergyComparison

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile91
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.cheegerHeat_weightedEnergy_compact {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (f F : X →ᵇ ℝ)
    (hf : GloballyLipschitz (f : X → ℝ)) (hfc : HasCompactSupport (f : X → ℝ))
    (hFl : GloballyLipschitz (F : X → ℝ)) (hf2 : MemLp f 2 m) {t : ℝ} (ht : 0 ≤ t)
    (hF : F =ᵐ[m] cheegerHeat h t (hf2.toLp f))
    (u : Lp ℝ 2 m) (hu : Integrable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x) :
    cheegerEnergy (densityMeasure m u) F ≤
      ENNReal.ofReal (Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(localSlope f x).toReal^2 ∂m)/2) := by
  let : IsFiniteMeasure (densityMeasure m u) := finite_densityMeasure u hu
  have H := energy_le_of_hopf_integral_comparison f F hf.choose_spec hFl.choose_spec
    (hrcd.1.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hu ht).1
    (cheegerHeat_nonneg h ht u hun) (Real.exp_pos (2*K*t))
    (fun s hs => hrcd.hopf_heat_integral_commutation hN hfull hfin h o f F hf hfc hf2 ht hF u hu hun hs)
  convert H using 1
  congr 1
  rw [show -2*K*t = -(2*K*t) by ring,Real.exp_neg]
  ring

omit [ProperSpace X] [SigmaFinite m] in
lemma weighted_gradient_le_energy (u : Lp ℝ 2 m) (hu : Integrable u m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hm : m ≪ densityMeasure m u)
    (hνm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      (densityMeasure m u).restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m)
    (hmν : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      m.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • densityMeasure m u)
    (F : X →ᵇ ℝ) (hF : GloballyLipschitz (F : X → ℝ)) :
    ENNReal.ofReal ((∫ x,u x*(weakGradient m F x)^2 ∂m)/2) ≤ cheegerEnergy (densityMeasure m u) F := by
  let ν := densityMeasure m u
  let : IsFiniteMeasure ν := finite_densityMeasure u hu
  have hF2 := (F.memLp_top (μ := ν)).mono_exponent (show (2:ℝ≥0∞) ≤ ∞ from le_top)
  have hfin := (cheegerEnergy_le_integral_localSlope ν hF.choose_spec hF2).trans_lt ENNReal.ofReal_lt_top
  obtain ⟨D,hD,hE⟩ := exists_minimalGradient_energy_le_cheeger (m := ν) (fun _ _ => measure_lt_top _ _) hF2 hfin
  have hchange : weakGradient m F =ᵐ[m] weakGradient ν F :=
    weakGradient_eq_of_locally_comparable (densityMeasure_ac m u) hm hνm hmν F
  have hchangeν : weakGradient m F =ᵐ[ν] weakGradient ν F :=
    (densityMeasure_ac m u).ae_le hchange
  have hDm : weakGradient m F =ᵐ[ν] D :=
    Filter.EventuallyEq.trans hchangeν (weakGradient_ae_eq_of_isMinimal hD)
  have he : (∫ x,u x*(weakGradient m F x)^2 ∂m) = ‖D‖^2 := by
    rw [← integral_densityMeasure m u hun]
    have heq : (fun x => weakGradient m F x ^ 2) =ᵐ[ν] (fun x => (D x)^2) := by
      filter_upwards [hDm] with x hx
      rw [hx]
    change (∫ x,weakGradient m F x ^ 2 ∂ν) = _
    rw [integral_congr_ae heq]
    simpa only [Lp.toLp_coeFn] using (norm_toLp_sq_eq_integral (Lp.memLp D)).symm
  rwa [he]

lemma RCD.cheegerHeat_weightedGradient_compact {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (f F : X →ᵇ ℝ)
    (hf : GloballyLipschitz (f : X → ℝ)) (hfc : HasCompactSupport (f : X → ℝ))
    (hFl : GloballyLipschitz (F : X → ℝ)) (hf2 : MemLp f 2 m) {t : ℝ} (ht : 0 ≤ t)
    (hF : F =ᵐ[m] cheegerHeat h t (hf2.toLp f))
    (u : Lp ℝ 2 m) (hu : Integrable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hm : m ≪ densityMeasure m u)
    (hνm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      (densityMeasure m u).restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m)
    (hmν : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      m.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • densityMeasure m u) :
    (∫ x,u x*(weakGradient m F x)^2 ∂m) ≤
      Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(localSlope f x).toReal^2 ∂m) := by
  have H := (weighted_gradient_le_energy u hu hun hm hνm hmν F hFl).trans
    (hrcd.cheegerHeat_weightedEnergy_compact hN hfull hfin h o f F hf hfc hFl hf2 ht hF u hu hun)
  have Hn : 0 ≤ Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(localSlope f x).toReal^2 ∂m)/2 := by
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg (Real.exp_pos _).le
    exact integral_nonneg_of_ae ((cheegerHeat_nonneg h ht u hun).mono fun x hx => mul_nonneg hx (sq_nonneg _))
  have HH := (ENNReal.ofReal_le_ofReal_iff Hn).mp H
  linarith
end WeakHessian

end

end InlinedFile91

end OAI
