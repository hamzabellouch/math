import OAI.Geometry.Convex.GeneralMahler.ProjMean

namespace OAI
/-! Unique mean-bias choice (§02, biased projection lemma). We solve
for arbitrary interior means w, later inserting the bias curve. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real Metric
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ} (C : ProperCone ℝ (Rn m)) (B : Rn m ≃L[ℝ] Rn m)

def meanEnergy (a : Rn m) := ∫ x, energy C (affineN B a x) ∂normal m

lemma energy_integrable (a : Rn m) :
    Integrable (fun x => energy C (affineN B a x)) (normal m) := by
  change Integrable (fun x => ‖sample C B a x‖^2 / 2) (normal m)
  apply Integrable.div_const _ 2
  exact ((poly_sample C B a).norm.pow 2).gaussian_integrable
    (((continuous_sample C B a).norm.pow 2).aestronglyMeasurable)

theorem meanEnergy_derivative (a : Rn m) :
    HasFDerivAt (meanEnergy C B) (innerSL ℝ (mean C B a)) a := by
  let F := fun (b x : Rn m) => energy C (affineN B b x)
  have hm (b : Rn m) : Continuous (F b) := by
    exact ((continuous_sample C B b).norm.pow 2).div_const 2
  let D := fun (b x : Rn m) => innerSL ℝ (sample C B b x)
  have hD : Continuous (D a) :=
    (innerSL ℝ).continuous.comp (continuous_sample C B a)
  have he : innerSL ℝ (mean C B a) = ∫ x, D a x ∂normal m :=
    ((show (Rn m) →L[ℝ] (Rn m) →L[ℝ] ℝ from innerSL ℝ).integral_comp_comm
      (sample_integrable ..)).symm
  rw [he]
  let g := fun (x:Rn m) => ‖sample C B a x‖+1
  have hi : Integrable g (normal m) := (sample_integrable ..).norm.add (integrable_const _)
  change HasFDerivAt (fun b => ∫ x, F b x ∂_) _ a
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds a zero_lt_one)
    (Eventually.of_forall fun y => (hm y).aestronglyMeasurable)
    (energy_integrable ..) hD.aestronglyMeasurable _ hi _
  · apply ae_of_all
    intro x b hb
    change ‖innerSL ℝ _‖ ≤ g x
    rw [innerSL_apply_norm]
    have HH : ‖sample C B b x - sample C B a x‖ < 1 := lt_of_le_of_lt (by
      simpa only [sample, affineN, ← dist_eq_norm, dist_add_left,NNReal.coe_one,one_mul] using
        (coneProj_lip C).dist_le_mul (B x + b) (B x + a)) (show dist b a < 1 from hb)
    have hh := norm_add_le (sample C B b x-sample C B a x) (sample C B a x)
    rw [sub_add_cancel] at hh
    dsimp only [g]; linarith
  · apply ae_of_all
    intro x b _
    have h := energy_hasFDeriv C (B x + b)
    simpa only [F,D,sample,affineN,Function.comp_def,zero_add,ContinuousLinearMap.comp_id] using
      h.comp b ((hasFDerivAt_const (B x) b).add (hasFDerivAt_id b))

def dualEnergy (w a : Rn m) := meanEnergy C B a - ⟪w,a⟫

theorem dualEnergy_derivative (w a : Rn m) :
    HasFDerivAt (dualEnergy C B w) (innerSL ℝ (mean C B a-w)) a := by
  rw [map_sub]
  exact (meanEnergy_derivative C B a).sub (innerSL ℝ w).hasFDerivAt

lemma meanEnergy_lower (a y : Rn m) (hy : y ∈ C) :
    ⟪y,a⟫-‖y‖^2/2 ≤ meanEnergy C B a := by
  let f := affineN B a
  have hi := affineN_integrable B a
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ y
  have H : ∫ x, (l (f x)-‖y‖^2/2) ∂normal m ≤ meanEnergy C B a :=
    integral_mono ((l.integrable_comp hi).sub (integrable_const _))
      (energy_integrable ..) (fun x => energy_lower C _ hy)
  rw [integral_sub (l.integrable_comp hi) (integrable_const _), integral_const,
    l.integral_comp_comm hi,affineN_mean B a] at H
  simpa [l] using H

-- explicit bound also useful for uniform estimates
theorem dualEnergy_lower (w a : Rn m)
    {r : ℝ} (hr : 0 < r) (hu : closedBall w r ⊆ C) :
    r*‖a‖-(‖w‖+r)^2/2 ≤ dualEnergy C B w a := by
  by_cases ha : a = 0
  · subst a
    rw [dualEnergy]
    have h := meanEnergy_lower C B (0 : Rn m) 0 C.zero_mem
    simp only [inner_zero_right,norm_zero] at *
    nlinarith
  let d := (r/‖a‖) • a
  have hap : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hh : ‖d‖ = r := by
    simp only [d,norm_smul, Real.norm_eq_abs,abs_of_pos (div_pos hr hap)]
    field_simp
  have h : w+d ∈ C := hu (by rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,hh])
  have he : ⟪d,a⟫ = r * ‖a‖ := by
    simp only [d,real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp
  have hx : ‖w+d‖ ≤ ‖w‖+r := by simpa only [← hh] using norm_add_le w d
  have H := meanEnergy_lower C B a (w+d) h
  rw [inner_add_left,he] at H
  rw [dualEnergy]
  nlinarith [norm_nonneg (w+d)]

theorem bias_exists (w : Rn m) (hw : w ∈ interior (C : Set (Rn m))) :
    ∃ a, mean C B a = w := by
  obtain ⟨r,hr,hu⟩ := nhds_basis_closedBall.mem_iff.mp (mem_interior_iff_mem_nhds.mp hw)
  have h := dualEnergy_lower C B w (r := r)
  have hf : Continuous (dualEnergy C B w) := continuous_iff_continuousAt.mpr
    fun x => (dualEnergy_derivative C B w x).continuousAt
  have ht : Tendsto (dualEnergy C B w) (cocompact (Rn m)) atTop := by
    apply tendsto_atTop_mono _ ((tendsto_norm_cocompact_atTop.const_mul_atTop hr).atTop_add
      (g := fun _ => -((‖w‖+r)^2/2)) tendsto_const_nhds)
    intro x; simpa only [← sub_eq_add_neg] using h x hr hu
  obtain ⟨x,hx⟩ := hf.exists_forall_le ht
  have he := IsLocalMin.hasFDerivAt_eq_zero (f := dualEnergy C B w)
    (a := x) (Eventually.of_forall hx) (dualEnergy_derivative C B w x)
  refine ⟨x, sub_eq_zero.mp ?_⟩
  have hp := congrFun (congrArg DFunLike.coe he) (mean C B x - w)
  change ⟪mean C B x-w,mean C B x-w⟫ = 0 at hp
  simpa using hp

lemma pd_equiv {A : Mat m} (h : A.PosDef) :
    ∃ e : Rn m ≃L[ℝ] Rn m, (e:Rn m →L[ℝ] Rn m) = op A := by
  let a : Rn m →ₗ[ℝ] Rn m := (op A).toLinearMap
  have hh : Function.Injective a := by
    intro x y hxy
    by_contra hn
    have hu := (op_posDef_iff.mp h).2 (x-y) (sub_ne_zero.mpr hn)
    have hb : op A (x-y) = 0 := by change a _ = 0; rw [_root_.map_sub,hxy,sub_self]
    rw [hb, inner_zero_right] at hu
    exact (lt_irrefl _ hu)
  let e := LinearEquiv.ofBijective a ⟨hh,LinearMap.injective_iff_surjective.mp hh⟩
  exact ⟨e.toContinuousLinearEquiv, by rfl⟩

theorem mean_injective (hc : (interior (C:Set (Rn m))).Nonempty) :
    Function.Injective (mean C B) := by
  intro x y h
  by_contra hn
  let v := y-x
  have hv : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
  let L := fun r:ℝ => x+r • v
  let g := fun r => ⟪v,mean C B (L r)⟫
  have he : StrictMono g := by
    apply strictMono_of_deriv_pos
    intro r
    have hd : HasDerivAt L v r := by
      change HasDerivAt ((fun _:ℝ=>x) + (fun t:ℝ=>t • v)) v r
      simpa only [one_smul,zero_add] using
        ((hasDerivAt_const r x).add ((hasDerivAt_id' r).smul_const v))
    have hg : HasDerivAt g ⟪v,op (meanJac C B (L r)) v⟫ r :=
      (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt r
        ((hasFDerivAt_mean C B _).comp_hasDerivAt r hd)
    rw [hg.deriv]
    exact (op_posDef_iff.mp (mean_pos C B hc _)).2 v hv
  have hh := he zero_lt_one
  simp only [g,L,zero_smul,one_smul,add_zero,v,add_sub_cancel] at hh
  rw [h] at hh
  exact lt_irrefl _ hh

/-- Unique bias at an interior mean; arbitrary value outside interior. -/
def bias (w : Rn m) : Rn m :=
  open Classical in if hw : w ∈ interior (C:Set (Rn m)) then
    (bias_exists C B w hw).choose else 0

theorem bias_mean (w : Rn m) (hw : w ∈ interior (C:Set (Rn m))) :
    mean C B (bias C B w) = w := by
  unfold bias; rw [dite_eq_left hw]
  exact (bias_exists C B w hw).choose_spec

theorem bias_C_one (w : Rn m) (hw : w ∈ interior (C:Set (Rn m))) :
    ContDiffAt ℝ 1 (bias C B) w := by
  let a := bias C B w
  have ha := bias_mean C B w hw
  obtain ⟨e,he⟩ := pd_equiv (mean_pos C B ⟨w,hw⟩ a)
  have h' : HasStrictFDerivAt (mean C B) (e : Rn m →L[ℝ] Rn m) a := by
    rw [he, ← (hasFDerivAt_mean C B a).fderiv]
    exact (mean_C_one C B).hasStrictFDerivAt (by simp)
  let f := h'.localInverse (mean C B) e a
  have hi : f =ᶠ[𝓝 w] bias C B := by
    have ht : mean C B a = w := ha
    have hy := h'.eventually_right_inverse
    rw [ht] at hy
    filter_upwards [hy,isOpen_interior.mem_nhds hw] with y hf hy
    exact mean_injective C B ⟨w,hw⟩ (hf.trans (bias_mean C B y hy).symm)
  have hr : ContDiffAt ℝ 1 f (mean C B a) :=
    (mean_C_one C B).contDiffAt.to_localInverse h'.hasFDerivAt (by norm_num)
  rw [show mean C B a = w from ha] at hr
  exact hr.congr_of_eventuallyEq hi.symm

end GeneralMahler

end

end OAI
