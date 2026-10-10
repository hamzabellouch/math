import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.OriginalBochner
import OAI.Geometry.WeakHessian.HeatFlow.HeatSobolevTime
import OAI.Geometry.WeakHessian.Sobolev.WeightedGradientLoss
import OAI.Geometry.WeakHessian.HeatFlow.HeatEnergyQuotient

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile104
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.gradientSquare_sobolev {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hA : Sobolev m (A : X → ℝ)) {L : ℝ} (hL : 0 ≤ L)
    (hub : ∀ᵐ x ∂m,weakGradient m (u : X → ℝ) x ≤ L) :
    Sobolev m (fun x => (weakGradient m (u : X → ℝ) x)^2) := by
  have hus : Sobolev m (u : X → ℝ) := (hrcd.1.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp u)).mpr hu.1
  have hDuabs : ∀ᵐ x ∂m,|weakGradient m (u : X → ℝ) x| ≤ L := by
    filter_upwards [hub,weakGradient_nonneg (m := m) (u : X → ℝ)] with x hx hn; rwa [abs_of_nonneg hn]
  have hq : MemLp (fun x => (weakGradient m (u : X → ℝ) x)^2) 2 m := by
    simpa only [pow_two] using memLp_mul_bounded hus.2.2 hus.2.2.aestronglyMeasurable hDuabs
  let q := hq.toLp (fun x => (weakGradient m (u : X → ℝ) x)^2)
  let D := hus.2.2.toLp (weakGradient m (u : X → ℝ))
  let DA := hA.2.2.toLp (weakGradient m (A : X → ℝ))
  have hD : IsMinimalLocalWeakUpperGradient m (u : X → ℝ) D :=
    (weakGradient_isMinimal hus.2.1.2).congr_ae .rfl hus.2.2.coeFn_toLp.symm
  have hDA : IsLocalWeakUpperGradient m (A : X → ℝ) DA :=
    (weakGradient_isMinimal hA.2.1.2).1.congr_ae .rfl hA.2.2.coeFn_toLp.symm
  have hqi : Integrable q m := hus.2.2.integrable_sq.congr hq.coeFn_toLp.symm
  have hqn : ∀ᵐ x ∂m,0 ≤ q x := by filter_upwards [hq.coeFn_toLp] with x hx; rw [hx]; positivity
  have hqb : ∀ᵐ x ∂m,|q x| ≤ L^2 := by
    filter_upwards [hq.coeFn_toLp,hDuabs] with x hx hb
    rw [hx,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hL).mpr hb
  have hqb' : ∀ᵐ x ∂m,q x ≤ L^2 := hqb.mono fun x hx => (le_abs_self _).trans hx
  have hself : (∫ x,q x*(weakGradient m (u : X → ℝ) x)^2 ∂m) = ⟪q,q⟫_ℝ :=
    integral_Lp_function_eq_inner q hq
  let B := 2*L^2*‖D‖*‖DA‖
  have H (t : ℝ) (ht : 0 < t) :
      ⟪q,q⟫_ℝ-⟪q,cheegerHeat h t q⟫_ℝ ≤
        (1-Real.exp (2*K*t))*⟪q,q⟫_ℝ+Real.exp (2*K*t)*B*t := by
    have hvt := hrcd.cheegerHeat_sobolev hfin h o hD ht.le
    obtain ⟨E,hE,hEn⟩ := hrcd.1.cheegerHeat_difference_upperGradient hfin h o hu hDA ht
    have hloss := weighted_gradient_loss hfin hus hvt hE (Lp.memLp q).aestronglyMeasurable hqn (sq_nonneg L) hqb
    rw [hself] at hloss
    have hvn := hrcd.1.cheegerHeat_minimal_norm hfin h o hus ht.le hvt
    have hbn : 0 ≤ ‖D‖+‖hvt.2.2.toLp (weakGradient m (cheegerHeat h t u : X → ℝ))‖ := by positivity
    have hbn' : 0 ≤ t*‖DA‖ := mul_nonneg ht.le (norm_nonneg _)
    have hlow : ⟪q,q⟫_ℝ-(∫ x,q x*(weakGradient m (cheegerHeat h t u : X → ℝ) x)^2 ∂m) ≤ B*t := by
      apply hloss.trans
      calc
        _ ≤ L^2*(t*‖DA‖)*(‖D‖+‖hvt.2.2.toLp (weakGradient m (cheegerHeat h t u : X → ℝ))‖) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEn (sq_nonneg L)) hbn
        _ ≤ L^2*(t*‖DA‖)*(‖D‖+‖D‖) := by
          exact mul_le_mul_of_nonneg_left (add_le_add_right hvn _) (mul_nonneg (sq_nonneg L) hbn')
        _ = B*t := by dsimp [B]; ring
    have hhi := hrcd.cheegerHeat_gradient_integral hN hfull hfin h o hD ht.le q hqi hqn (sq_nonneg L) hqb'
    have heq : (∫ x,cheegerHeat h t q x*(D x)^2 ∂m) = ⟪q,cheegerHeat h t q⟫_ℝ := by
      rw [← integral_Lp_function_eq_inner (cheegerHeat h t q) hq]
      exact integral_congr_ae (by filter_upwards [hus.2.2.coeFn_toLp] with x hx; rw [hx])
    rw [heq] at hhi
    have hex : Real.exp (2*K*t)*Real.exp (-2*K*t) = 1 := by
      rw [← Real.exp_add,show 2*K*t+ -2*K*t = 0 by ring,Real.exp_zero]
    have hm := mul_le_mul_of_nonneg_left hhi (Real.exp_pos (2*K*t)).le
    rw [← mul_assoc,hex,one_mul] at hm
    have hh := mul_le_mul_of_nonneg_left hlow (Real.exp_pos (2*K*t)).le
    nlinarith
  have hder : HasDerivWithinAt (fun t : ℝ => 1-Real.exp (2*K*t)) (-2*K) (Ici 0) 0 := by
    convert! (((hasDerivWithinAt_id 0 (Ici 0)).const_mul (2*K)).exp).const_sub 1 using 1
    simp
  have hlim0 : Tendsto (fun t : ℝ => (1-Real.exp (2*K*t))/t) (𝓝[>] 0) (𝓝 (-2*K)) := by
    have HH := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp hder.Ioi_of_Ici
    change Tendsto (fun t => slope (fun t : ℝ => 1-Real.exp (2*K*t)) 0 t) _ _ at HH
    simpa only [slope_def_field,mul_zero,Real.exp_zero,sub_self,sub_zero] using HH
  have hexlim : Tendsto (fun t : ℝ => Real.exp (2*K*t)) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => Real.exp (2*K*t)) := by fun_prop
    simpa using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun t : ℝ => ((1-Real.exp (2*K*t))/t)*⟪q,q⟫_ℝ+Real.exp (2*K*t)*B)
      (𝓝[>] 0) (𝓝 ((-2*K)*⟪q,q⟫_ℝ+B)) := by
    simpa only [one_mul] using (hlim0.mul_const ⟪q,q⟫_ℝ).add (hexlim.mul_const B)
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0, ⟪q,q⟫_ℝ-⟪q,cheegerHeat h t q⟫_ℝ ≤
      (((-2*K)*⟪q,q⟫_ℝ+B)+1)*t := by
    filter_upwards [self_mem_nhdsWithin,hlim.eventually_lt_const (lt_add_one _)] with t ht hb
    change 0 < t at ht
    have HH := mul_le_mul_of_nonneg_right hb.le ht.le
    have he : (((1-Real.exp (2*K*t))/t)*⟪q,q⟫_ℝ+Real.exp (2*K*t)*B)*t =
        (1-Real.exp (2*K*t))*⟪q,q⟫_ℝ+Real.exp (2*K*t)*B*t := by field_simp [ht.ne']
    rw [he] at HH
    exact (H t ht).trans HH
  have hc := cheegerEnergy_le_of_eventual_heat_quotient hfin h q hb
  apply (hrcd.1.global_sobolev_iff_cheeger_lt_top hfin o hq).mpr
  rw [← cheegerEnergy_congr_ae hq.coeFn_toLp]
  exact hc.trans_lt ENNReal.ofReal_lt_top
end WeakHessian

end
end InlinedFile104

end OAI
