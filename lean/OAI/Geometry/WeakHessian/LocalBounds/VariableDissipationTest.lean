import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatVariableDissipation
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatGammaL2
import OAI.Geometry.WeakHessian.HeatFlow.BoundedSecondGenerator
import OAI.Geometry.WeakHessian.Calculus.VariableDissipationLimits

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_variable_bounded_test {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af AAf ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    (hAf : (cheeger_closedQuadraticEnergy h).IsFormGenerator Af AAf)
    {Cf CAf CAAf Cξ : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf) (hCAAf : 0 ≤ CAAf)
    (hCξ : 0 ≤ Cξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Af x| ≤ CAf)
    (hAAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|AAf x| ≤ CAAf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) :
    2*(∫ s in 0..T,∫ x,(cheegerHeat h s ξ x*(K-a*G x))*
      gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x
        ∂exponentialMeasure m (fun x => a*F x)) ≤
      (∫ x,cheegerHeat h T ξ x*gamma (exponentialMeasure m (fun x => a*F x)) f f x
        ∂exponentialMeasure m (fun x => a*F x))-
      (∫ x,ξ x*gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T f) (cheegerHeat h T f) x
        ∂exponentialMeasure m (fun x => a*F x)) := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsLocallyFiniteMeasure ν := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hnfin _ Metric.isBounded_ball⟩⟩
  let ts : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hts (n : ℕ) : 0 < ts n := by dsimp [ts]; positivity
  have ht0 : Tendsto ts atTop (𝓝 0) := by
    simpa only [ts,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose vs As AAs he hg hAg hvb hAb hAAb using
    (fun n => cheeger_double_resolvent_core h (hts n) hCξ ξ hξb)
  have hvs0 (n : ℕ) : ∀ᵐ x ∂ν,0 ≤ vs n x := by
    rw [he n]; exact cheeger_double_resolvent_nonneg h (hts n) ξ hξ0
  have hvs : Tendsto vs atTop (𝓝 ξ) := by
    have H := cheeger_double_resolvent_tendsto h hts ht0 ξ
    exact H.congr (fun n => (he n).symm)
  have hΓ (t : ℝ) (ht : 0 ≤ t) :
      MemLp (gamma ν (cheegerHeat h t f) (cheegerHeat h t f)) 2 ν :=
    hrcd.weighted_heat_gamma_memLp hN hfull hfin o hV hVB h hf hCf hCAf hfb hAfb ht
  have hΓ0 : MemLp (gamma ν f f) 2 ν := by
    simpa only [cheegerHeat_zero,one_apply_eq_self] using hΓ 0 le_rfl
  have hid (v : Lp ℝ 2 ν) {q : X → ℝ} (hq : MemLp q 2 ν) :
      (∫ x,v x*q x ∂ν) = ⟪hq.toLp q,v⟫_ℝ := by
    simpa only [Lp.toLp_coeFn] using integral_mul_eq_inner (Lp.memLp v) hq
  have hleft : Tendsto (fun n => ∫ x,vs n x*gamma ν (cheegerHeat h T f) (cheegerHeat h T f) x ∂ν)
      atTop (𝓝 (∫ x,ξ x*gamma ν (cheegerHeat h T f) (cheegerHeat h T f) x ∂ν)) := by
    simp only [hid _ (hΓ T hT)]
    exact (tendsto_const_nhds (x := (hΓ T hT).toLp _)).inner hvs
  have hright : Tendsto (fun n => ∫ x,cheegerHeat h T (vs n) x*gamma ν f f x ∂ν)
      atTop (𝓝 (∫ x,cheegerHeat h T ξ x*gamma ν f f x ∂ν)) := by
    simp only [hid _ hΓ0]
    simpa only [Function.comp_def] using (tendsto_const_nhds (x := hΓ0.toLp _)).inner
      ((cheegerHeat h T).continuous.tendsto ξ |>.comp hvs)
  let k := fun x => K-a*G x
  let B := |K|+|a| *CG
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hkm : AEStronglyMeasurable k ν :=
    (continuous_const.sub (continuous_const.mul hGc)).aestronglyMeasurable
  have hkb : ∀ᵐ x ∂ν, |k x| ≤ B := ae_of_all _ fun x =>
    (abs_sub _ _).trans (by dsimp only [B]; rw [abs_mul]; gcongr; exact hGb x)
  let Z := fun (v : Lp ℝ 2 ν) s => ∫ x, (cheegerHeat h s v x*k x)*
    gamma ν (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂ν
  have hZ (v : Lp ℝ 2 ν) : ContinuousOn (Z v) (Icc 0 T) :=
    hrcd.weighted_heat_curvature_continuousOn hN hfull hfin o hV hVB h v hf hCf hCAf hfb hAfb hkm hkb T
  have hZlim (s : ℝ) (hs : s ∈ Icc 0 T) :
      Tendsto (fun n => Z (vs n) s) atTop (𝓝 (Z ξ s)) := by
    have hq := memLp_mul_bounded (hΓ (T-s) (sub_nonneg.mpr hs.2)) hkm hkb
    have H := (tendsto_const_nhds (x := hq.toLp _)).inner (𝕜 := ℝ)
      ((cheegerHeat h s).continuous.tendsto ξ |>.comp hvs)
    have hrepr (v : Lp ℝ 2 ν) : Z v s = ⟪hq.toLp _,cheegerHeat h s v⟫_ℝ := by
      rw [← hid _ hq]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only; ring
    simpa only [hrepr,Function.comp_def] using H
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hfS : Sobolev ν (f : X → ℝ) :=
    (identified_sobolev_iff_energy hnfin hID).mpr hf.1
  have hZbound (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 T) :
      ‖Z (vs n) s‖ ≤ (Cξ*B)*(2*(cheegerEnergy ν (f : X → ℝ)).toReal) := by
    simpa only [Real.norm_eq_abs,Z] using abs_weighted_heat_gamma_le hnfin hID h hfS hCξ
      (hvb n) hkm hB hkb hs.1 (sub_nonneg.mpr hs.2)
  have htime : Tendsto (fun n => ∫ s in 0..T, Z (vs n) s) atTop (𝓝 (∫ s in 0..T, Z ξ s)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (Cξ*B)*(2*(cheegerEnergy ν (f : X → ℝ)).toReal))
    · exact Eventually.of_forall fun n => ((hZ (vs n)).mono (by
        rw [uIoc_of_le hT]; exact Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_uIoc
    · exact Eventually.of_forall fun n => ae_of_all _ fun s hs => hZbound n s (by
        rw [uIoc_of_le hT] at hs; exact ⟨hs.1.le,hs.2⟩)
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun s hs => hZlim s (by rw [uIoc_of_le hT] at hs; exact ⟨hs.1.le,hs.2⟩)
  apply le_of_tendsto_of_tendsto (htime.const_mul 2) (hright.sub hleft)
    (Eventually.of_forall fun n => ?_)
  exact hHess.rcd_weighted_heat_variable_dissipation hN hrcd hfull hfin o hF hFb hGb hGc ha h
    hf hAf (hg n) (hAg n) hCf hCAf hCAAf hCξ (by positivity)
    hfb hAfb hAAfb (hvb n) (hAb n) (hvs0 n) hT
end WeakHessian

end
end

end OAI
