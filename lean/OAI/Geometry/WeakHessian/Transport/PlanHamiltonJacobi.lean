import Mathlib
import OAI.Geometry.WeakHessian.Transport.ScaledPlanYoung

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile221
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsTestPlan.hamiltonJacobi_upper_slope (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π,IsGeodesic γ) {W : ℝ → X → ℝ}
    (hW : ∀ t,LocallyL2 m (W t)) (hW0 : LocalSobolev m (W 0))
    {q C : ℝ} (hq : 0 < q) (hC : 0 < C)
    (hHJ : ∀ t,0 < t → t ≤ 1 → ∀ᵐ x ∂m,
      W t x-W 0 x ≤ (-t*q/(2*(q+t)))*C*(weakGradient m (W 0) x)^2)
    {b : ℝ} (hb' : (∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π)/(2*C) < b) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      ((∫ γ,W t (evalReal γ t) ∂π)-(∫ γ,W 0 (γ timeZero) ∂π))/t < b := by
  let D := weakGradient m (W 0)
  let E := ∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π
  let A := fun t : ℝ => ∫ γ,(D (evalReal γ t))^2 ∂π
  let Z := ∫ γ,(D (γ timeZero))^2 ∂π
  let B := fun t : ℝ => (-q/(2*(q+t)))*C*A t+
    C/2*((∫ s in 0..t,A s)/t)+E/(2*C)
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hA : Tendsto A (𝓝[>] 0) (𝓝 Z) := by
    have H : Tendsto (fun s : ℝ => ∫ γ,(weakGradient m (W 0) (evalReal γ s))^2 ∂π)
        (𝓝[>] 0) (𝓝 (∫ γ,(weakGradient m (W 0) (evalReal γ 0))^2 ∂π)) :=
      (hπ.continuous_local_gradient_energy hfin hb hW0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [A,Z,D,evalReal,show clampTime 0 = timeZero from Subtype.ext (by simp [clampTime,timeZero])] using H
  have hAv := hπ.tendsto_average_local_gradient_energy hfin hb hW0
  have hrat : Tendsto (fun t : ℝ => (-q/(2*(q+t)))*C) (𝓝[>] 0) (𝓝 (-C/2)) := by
    have H : Tendsto (fun t : ℝ => (-q/(2*(q+t)))*C) (𝓝[>] 0)
        (𝓝 (-q/(2*(q+0))*C)) := ((tendsto_const_nhds (x := -q)).div
      ((hid.const_add q).const_mul 2) (by positivity : 2*(q+0) ≠ 0)).mul_const C
    have he : -q/(2*(q+0))*C = -C/2 := by field_simp [hq.ne']; ring
    rwa [he] at H
  have hB : Tendsto B (𝓝[>] 0) (𝓝 (E/(2*C))) := by
    convert ((hrat.mul hA).add (hAv.const_mul (C/2))).add_const (E/(2*C)) using 1
    dsimp only [B,A,Z,D]
    congr 1
    ring
  have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0,t < 1 := hid.eventually_lt_const (by norm_num)
  filter_upwards [hB.eventually_lt_const hb',self_mem_nhdsWithin,hlt] with t hbt ht ht1
  change 0 < t at ht
  let τ : Time := ⟨t,ht.le,ht1.le⟩
  have hc : clampTime t = τ := Subtype.ext (clampTime_of_mem τ.property)
  have hD := (weakGradient_isMinimal hW0.2).1
  have hY := hD.geodesic_young_time_scaled hW0.1.aemeasurable hπ hb hgeo hC τ ht
  have htemporal : (∫ γ,W t (γ τ)-W 0 (γ τ) ∂π) ≤
      (-t*q/(2*(q+t)))*C*A t := by
    simp only [A,evalReal,hc]
    rw [← integral_const_mul]
    apply integral_mono_ae ((hW t).integrable_eval hfin hπ hb τ |>.sub
      ((hW 0).integrable_eval hfin hπ hb τ))
      ((hD.1.integrable_sq_eval hπ hb τ).const_mul _)
    filter_upwards [hπ.ae_eval_of_ae (hHJ t ht ht1.le) τ] with γ hγ
    exact hγ
  have he : (∫ γ,W t (evalReal γ t) ∂π)-(∫ γ,W 0 (γ timeZero) ∂π) =
      (∫ γ,W t (γ τ)-W 0 (γ τ) ∂π)+(∫ γ,W 0 (γ τ)-W 0 (γ timeZero) ∂π) := by
    rw [integral_sub ((hW t).integrable_eval hfin hπ hb τ) ((hW 0).integrable_eval hfin hπ hb τ),
      integral_sub ((hW 0).integrable_eval hfin hπ hb τ) ((hW 0).integrable_eval hfin hπ hb timeZero)]
    simp only [evalReal,hc]; ring
  have hsum := add_le_add htemporal hY
  have hbound : ((∫ γ,W t (evalReal γ t) ∂π)-(∫ γ,W 0 (γ timeZero) ∂π))/t ≤ B t := by
    apply (div_le_iff₀ ht).mpr
    rw [he]
    convert hsum using 1
    dsimp only [B,A,D,E,τ]
    field_simp [hC.ne',ne_of_gt ht]
    ring
  exact hbound.trans_lt hbt
end WeakHessian

end
end InlinedFile221

end OAI
