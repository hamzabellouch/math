import Mathlib
import OAI.Geometry.WeakHessian.Transport.PlanHamiltonJacobi

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile223
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X] in
lemma IsGeodesic.restrictCurve {γ : Curve X} (hγ : IsGeodesic γ) (a b : Time) :
    IsGeodesic (restrictCurve a b γ) := by
  intro s t
  change dist (γ (affineTime a b s)) (γ (affineTime a b t)) =
    |(s : ℝ)-(t : ℝ)| *dist (γ (affineTime a b timeZero)) (γ (affineTime a b timeOne))
  rw [affineTime_zero,affineTime_one,hγ (affineTime a b s) (affineTime a b t),hγ a b]
  have he : (affineTime a b s : ℝ)-(affineTime a b t : ℝ) =
      ((b : ℝ)-(a : ℝ))*((s : ℝ)-(t : ℝ)) := by dsimp [affineTime]; ring
  rw [he,abs_mul,abs_sub_comm (b : ℝ) (a : ℝ)]
  ring

lemma IsTestPlan.hamiltonJacobi_action_bound (hfin : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π,IsGeodesic γ) {W : ℝ → X → ℝ}
    (hW : ∀ r,LocallyL2 m (W r)) (hWS : ∀ r,0 < r → LocalSobolev m (W r))
    {C q : ℝ} (hC : 0 < C) (hq : 0 < q)
    (hHJ : ∀ r s,0 < r → r ≤ s → ∀ᵐ x ∂m,
      W s x-W r x ≤ (-(s-r)*r/(2*s))*C*(weakGradient m (W r) x)^2)
    (hcont : ContinuousOn (fun t : ℝ => ∫ γ,W (q+t) (evalReal γ t) ∂π) (Icc 0 1)) :
    (∫ γ,W (q+1) (γ timeOne) ∂π)-(∫ γ,W q (γ timeZero) ∂π) ≤
      (∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π)/(2*C) := by
  let : IsProbabilityMeasure π := hπ.1
  let E := ∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π
  let J := fun t : ℝ => ∫ γ,W (q+t) (evalReal γ t) ∂π
  suffices H : J 1 ≤ J 0+E/(2*C)*1 by
    have hz : clampTime 0 = timeZero := Subtype.ext (by simp [clampTime,timeZero])
    have ho : clampTime 1 = timeOne := Subtype.ext (by simp [clampTime,timeOne])
    simp only [J,E,evalReal,hz,ho,add_zero,mul_one] at H
    linarith
  apply image_le_of_liminf_slope_right_le_deriv_boundary (f := J)
    (B := fun t => J 0+E/(2*C)*t) (B' := fun _ => E/(2*C)) hcont (by simp)
    (by fun_prop) (fun x _ => by simpa using
      (((hasDerivAt_id x).const_mul (E/(2*C))).const_add (J 0)).hasDerivWithinAt (s := Ici x))
    _ ⟨zero_le_one,le_rfl⟩
  intro s hs r hr
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s < 1 := hs.2
  have hqs : 0 < q+s := add_pos_of_pos_of_nonneg hq hs0
  let a : Time := ⟨s,hs.1,hs.2.le⟩
  let c := 1-s
  have hc : 0 < c := sub_pos.mpr hs.2
  let π' := π.map (WeakHessian.restrictCurve a timeOne)
  have hp' : IsTestPlan m π' := hπ.restrictCurve a timeOne hs.2
  have hb' : BoundedTracks π' := hb.restrictCurve a timeOne
  have hg' : ∀ᵐ γ ∂π',IsGeodesic γ :=
    continuous_ae_map_of_ae (continuous_restrictCurve a timeOne)
      (hgeo.mono fun γ hγ => hγ.restrictCurve a timeOne)
  let V := fun t : ℝ => W (q+s+c*t)
  have hV0 : LocalSobolev m (V 0) := by simpa only [V,mul_zero,add_zero] using hWS (q+s) (by linarith)
  have hJ' (t : ℝ) (ht : 0 < t) (_ : t ≤ 1) : ∀ᵐ x ∂m,
      V t x-V 0 x ≤ (-t*((q+s)/c)/(2*((q+s)/c+t)))*(c*C)*(weakGradient m (V 0) x)^2 := by
    have H := hHJ (q+s) (q+s+c*t) (by linarith) (by nlinarith)
    have he : (-(q+s+c*t-(q+s))*(q+s)/(2*(q+s+c*t)))*C =
        (-t*((q+s)/c)/(2*((q+s)/c+t)))*(c*C) := by
      field_simp [hc.ne',show q+s+c*t ≠ 0 by positivity,
        show (q+s)/c+t ≠ 0 by positivity]
      ring
    simpa only [V,mul_zero,add_zero,he] using H
  have hE' : (∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π') = c^2*E := by
    have hm : AEStronglyMeasurable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) π' :=
      (by fun_prop : Continuous (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2)).aestronglyMeasurable
    change (∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π.map (WeakHessian.restrictCurve a timeOne)) = c^2*E
    rw [integral_map (continuous_restrictCurve a timeOne).measurable.aemeasurable hm]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hgeo] with γ hγ
    rw [restrictCurve_zero,restrictCurve_one,hγ a timeOne]
    have hh : |(a:ℝ)-(timeOne:ℝ)| = c := by
      change |s-1| = 1-s
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [hh,mul_pow]
  have hbr : (∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π')/(2*(c*C)) < c*r := by
    rw [hE']
    have he : c^2*E/(2*(c*C)) = c*(E/(2*C)) := by field_simp
    rw [he]
    exact mul_lt_mul_of_pos_left hr hc
  have H := hp'.hamiltonJacobi_upper_slope (W := V) hfin hb' hg' (fun t => hW (q+s+c*t)) hV0
    (show 0 < (q+s)/c by positivity) (mul_pos hc hC) hJ' hbr
  have hδ : Tendsto (fun z : ℝ => (z-s)/c) (𝓝[>] s) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [sub_self,zero_div] using
        ((by fun_prop : Continuous (fun z : ℝ => (z-s)/c)).tendsto s).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact div_pos (sub_pos.mpr hz) hc
  have hmap (t : ℝ) (g : X → ℝ) (hg : LocallyL2 m g) :
      (∫ γ,g (evalReal γ t) ∂π') = ∫ γ,g (evalReal (WeakHessian.restrictCurve a timeOne γ) t) ∂π :=
    integral_map (continuous_restrictCurve a timeOne).measurable.aemeasurable
      (hg.integrable_eval hfin hp' hb' (clampTime t)).aestronglyMeasurable
  have hz0 : (∫ γ,V 0 (γ timeZero) ∂π') = J s := by
    rw [integral_map (continuous_restrictCurve a timeOne).measurable.aemeasurable
      ((hW _).integrable_eval hfin hp' hb' timeZero).aestronglyMeasurable]
    simp only [mul_zero,add_zero,restrictCurve_zero,J]
    congr 1; funext γ
    rw [show evalReal γ s = γ a from congrArg γ (Subtype.ext (clampTime_of_mem a.property))]
  apply Filter.Eventually.frequently
  have hsmall : ∀ᶠ z : ℝ in 𝓝[>] s,z < 1 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun z : ℝ => z) (𝓝[>] s) (𝓝 s)).eventually_lt_const hs.2
  filter_upwards [hδ.eventually H,self_mem_nhdsWithin,hsmall] with z hz hsz hz1
  change s < z at hsz
  have hδ0 : 0 < (z-s)/c := div_pos (sub_pos.mpr hsz) hc
  have hδ1 : (z-s)/c ≤ 1 := (div_le_one hc).mpr (by dsimp [c]; linarith)
  rw [hmap _ _ (hW _),hz0] at hz
  have he : q+s+c*((z-s)/c) = q+z := by field_simp; ring
  have he' : (a:ℝ)+((timeOne:ℝ)-a)*((z-s)/c) = z := by
    change s+(1-s)*((z-s)/c) = z
    dsimp only [c]
    field_simp [show 1-s ≠ 0 from hc.ne']; ring
  have hid : (∫ γ,V ((z-s)/c) (evalReal (WeakHessian.restrictCurve a timeOne γ) ((z-s)/c)) ∂π) = J z := by
    dsimp only [V,J]
    simp_rw [he,evalReal_restrictCurve ⟨hδ0.le,hδ1⟩,he']
  rw [hid] at hz
  rw [slope_def_field]
  apply (div_lt_iff₀ (sub_pos.mpr hsz)).mpr
  have HH := (div_lt_iff₀ hδ0).mp hz
  have hh : c*r*((z-s)/c) = r*(z-s) := by field_simp
  rwa [hh] at HH
end WeakHessian

end
end InlinedFile223

end OAI
