import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.WeightedEnergyClosure

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile97
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma weighted_gradient_le_finite_energy (u : Lp ℝ 2 m) (hu : Integrable u m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hm : m ≪ densityMeasure m u)
    (hνm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      (densityMeasure m u).restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m)
    (hmν : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      m.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • densityMeasure m u)
    (F : X → ℝ) (hF2 : MemLp F 2 (densityMeasure m u))
    (hfin : cheegerEnergy (densityMeasure m u) F < ∞) :
    ENNReal.ofReal ((∫ x,u x*(weakGradient m F x)^2 ∂m)/2) ≤ cheegerEnergy (densityMeasure m u) F := by
  let ν := densityMeasure m u
  let : IsFiniteMeasure ν := finite_densityMeasure u hu
  obtain ⟨D,hD,hE⟩ := exists_minimalGradient_energy_le_cheeger (m := ν) (fun _ _ => measure_lt_top _ _) hF2 hfin
  have hchange := weakGradient_eq_of_locally_comparable (densityMeasure_ac m u) hm hνm hmν F
  have hDm : weakGradient m F =ᵐ[ν] D :=
    Filter.EventuallyEq.trans ((densityMeasure_ac m u).ae_le hchange) (weakGradient_ae_eq_of_isMinimal hD)
  have he : (∫ x,u x*(weakGradient m F x)^2 ∂m) = ‖D‖^2 := by
    rw [← integral_densityMeasure m u hun]
    have heq : (fun x => weakGradient m F x ^ 2) =ᵐ[ν] (fun x => (D x)^2) := by
      filter_upwards [hDm] with x hx; rw [hx]
    change (∫ x,weakGradient m F x ^ 2 ∂ν) = _
    rw [integral_congr_ae heq]
    simpa only [Lp.toLp_coeFn] using (norm_toLp_sq_eq_integral (Lp.memLp D)).symm
  rwa [he]

omit [CompleteSpace X] [SigmaFinite m] in
lemma RCD.cheegerHeat_sobolev {K N : ℝ}
    (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m) (o : X)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D) {t : ℝ} (ht : 0 ≤ t) :
    Sobolev m (cheegerHeat h t f : X → ℝ) := by
  apply (hrcd.1.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp _)).mpr
  exact (cheegerHeat_energy_le h ht f).trans_lt
    ((hrcd.1.global_cheegerEnergy_le_weak hfin o hD.1).trans_lt ENNReal.ofReal_lt_top)

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [SigmaFinite m] in
lemma integrable_bounded_weakGradient_sq {F u : X → ℝ} (hF : Sobolev m F)
    (hu : AEStronglyMeasurable u m) {B : ℝ} (huB : ∀ᵐ x ∂m,|u x| ≤ B) :
    Integrable (fun x => u x*(weakGradient m F x)^2) m := by
  apply hF.2.2.integrable_sq.bdd_mul hu
  simpa only [Real.norm_eq_abs] using huB

lemma RCD.cheegerHeat_weightedGradient {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D) {t : ℝ} (ht : 0 ≤ t)
    (u : Lp ℝ 2 m) (hu : Integrable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,u x ≤ B)
    (hm : m ≪ densityMeasure m u)
    (hνm : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      (densityMeasure m u).restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m)
    (hmν : ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      m.restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • densityMeasure m u) :
    (∫ x,u x*(weakGradient m (cheegerHeat h t f : X → ℝ) x)^2 ∂m) ≤
      Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(D x)^2 ∂m) := by
  have he := hrcd.cheegerHeat_weightedEnergy hN hfull hfin h o hD ht u hu hun hB huB
  have hf2 := (Lp.memLp (cheegerHeat h t f)).of_measure_le_smul ENNReal.ofReal_ne_top (densityMeasure_le_const huB)
  have H := (weighted_gradient_le_finite_energy u hu hun hm hνm hmν _ hf2
    (he.trans_lt ENNReal.ofReal_lt_top)).trans he
  have Hn : 0 ≤ Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(D x)^2 ∂m)/2 := by
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg (Real.exp_pos _).le
    exact integral_nonneg_of_ae ((cheegerHeat_nonneg h ht u hun).mono fun _ hx => mul_nonneg hx (sq_nonneg _))
  have HH := (ENNReal.ofReal_le_ofReal_iff Hn).mp H
  linarith

lemma RCD.cheegerHeat_gradient_integral {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f D : Lp ℝ 2 m}
    (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D) {t : ℝ} (ht : 0 ≤ t)
    (u : Lp ℝ 2 m) (hu : Integrable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,u x ≤ B) :
    (∫ x,u x*(weakGradient m (cheegerHeat h t f : X → ℝ) x)^2 ∂m) ≤
      Real.exp (-2*K*t)*(∫ x,cheegerHeat h t u x*(D x)^2 ∂m) := by
  obtain ⟨a,ha,hwi,hw,-⟩ := hrcd.1.exists_comparison_confinement hN hfull hfin o
  let w := hw.toLp (fun x => Real.exp (-(a*dist x o)))
  have hwi' : Integrable w m := hwi.congr hw.coeFn_toLp.symm
  have hwa : ∀ᵐ x ∂m,|w x| ≤ 1 := by
    filter_upwards [hw.coeFn_toLp] with x hx
    rw [hx,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [dist_nonneg (x := x) (y := o)])
  have hua : ∀ᵐ x ∂m,|u x| ≤ B := by
    filter_upwards [hun,huB] with x hx hy; rwa [abs_of_nonneg hx]
  have hHs := hrcd.cheegerHeat_sobolev hfin h o hD ht
  have hgu := integrable_bounded_weakGradient_sq hHs (Lp.memLp u).aestronglyMeasurable hua
  have hgw := integrable_bounded_weakGradient_sq hHs (Lp.memLp w).aestronglyMeasurable hwa
  have hsu := integrable_bounded_Lp_sq (Lp.memLp (cheegerHeat h t u)).aestronglyMeasurable (cheegerHeat_bounded h ht hB u hua) D
  have hsw := integrable_bounded_Lp_sq (Lp.memLp (cheegerHeat h t w)).aestronglyMeasurable (cheegerHeat_bounded h ht zero_le_one w hwa) D
  have H (ε : ℝ) (hε : 0 < ε) :
      (∫ x,u x*(weakGradient m (cheegerHeat h t f : X → ℝ) x)^2 ∂m)+
        ε*(∫ x,w x*(weakGradient m (cheegerHeat h t f : X → ℝ) x)^2 ∂m) ≤
      Real.exp (-2*K*t)*((∫ x,cheegerHeat h t u x*(D x)^2 ∂m)+
        ε*(∫ x,cheegerHeat h t w x*(D x)^2 ∂m)) := by
    have hpos := positiveProbe_pos o hw u hun hε
    have hbound := positiveProbe_le o ha hw u huB hε.le
    have HH := hrcd.cheegerHeat_weightedGradient hN hfull hfin h o hD ht
      (positiveProbe o hw u ε) (positiveProbe_integrable o hw u hu hwi ε) (hpos.mono fun _ hx => hx.le)
      (add_nonneg hB hε.le) hbound
      (densityMeasure_ac_of_pos _ hpos)
      (densityMeasure_locally_le _ (add_nonneg hB hε.le) hbound)
      (positiveProbe_locally_dominates o ha hw u hun hε)
    dsimp only [positiveProbe] at HH
    rw [integral_Lp_add_smul_mul u w _ hgu hgw,map_add,map_smul,
      integral_Lp_add_smul_mul _ _ _ hsu hsw] at HH
    exact HH
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have HH := le_of_tendsto_of_tendsto (tendsto_const_nhds.add (he.mul_const _))
    (tendsto_const_nhds.mul (tendsto_const_nhds.add (he.mul_const _)))
    (show ∀ᶠ ε in 𝓝[>] (0:ℝ),_ from by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact H ε hε)
  simpa only [zero_mul,add_zero] using HH
end WeakHessian

end
end InlinedFile97

end OAI
