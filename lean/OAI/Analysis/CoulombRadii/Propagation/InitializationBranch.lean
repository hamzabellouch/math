import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PropagationRegularity
import OAI.Analysis.CoulombRadii.Variational.WeakAdd

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

def initialPropagationOffset (bad : Prop) (Z r a : ℝ) (H : Position → ℝ) (x : Position) : ℝ :=
  (if bad then 0 else H x)-(7/10:ℝ)*Z/r+a*‖x‖^2

def initialPropagationError (bad : Prop) (r : ℝ) (μ : Position → ℝ) (x : Position) : ℝ :=
  if bad ∧ ‖x‖<r then μ x else 0

lemma initialPropagationOffset_continuous (bad : Prop) (Z r a : ℝ) {H : Position → ℝ}
    (hc : Continuous H) : Continuous (initialPropagationOffset bad Z r a H) := by
  unfold initialPropagationOffset
  by_cases hb : bad
  · simp only [ite_eq_left hb]
    fun_prop
  · simp only [ite_eq_right hb]
    exact (hc.sub continuous_const).add (continuous_const.mul (continuous_norm.pow 2))

lemma initialPropagationError_nonneg {bad : Prop} {r : ℝ} {μ : Position → ℝ}
    (hμ : ∀ x,0≤μ x) (x : Position) : 0 ≤ initialPropagationError bad r μ x := by
  unfold initialPropagationError
  split_ifs
  · exact hμ x
  · rfl

lemma initialPropagationError_support (bad : Prop) (r : ℝ) (μ : Position → ℝ)
    {x : Position} (hx : r≤‖x‖) : initialPropagationError bad r μ x=0 := by
  simp [initialPropagationError,not_lt_of_ge hx]

lemma initialPropagationError_measurable (bad : Prop) (r : ℝ) {μ : Position → ℝ}
    (hμ : Measurable μ) : Measurable (initialPropagationError bad r μ) := by
  unfold initialPropagationError
  by_cases hb : bad
  · simp only [hb,true_and]
    exact hμ.ite (isOpen_lt continuous_norm (continuous_const (y:=r))).measurableSet measurable_const
  · simp only [hb,false_and,ite_false]
    exact measurable_const

lemma initialPropagationError_ball_bounds {bad : Prop} {r : ℝ} {μ : Position → ℝ}
    (hμ : ∀ D : ℝ,∃ C : ℝ,∀ x∈Metric.closedBall 0 D,|μ x|≤C) :
    ∀ D : ℝ,∃ C : ℝ,∀ x∈Metric.closedBall 0 D,|initialPropagationError bad r μ x|≤C := by
  intro D
  obtain ⟨C,hC⟩ := hμ D
  refine ⟨max C 0,fun x hx => ?_⟩
  unfold initialPropagationError
  split_ifs
  · exact (hC x hx).trans (le_max_left _ _)
  · simpa only [abs_zero] using le_max_right C 0

lemma initial_core_source (bad : Prop) (r : ℝ) (μ : Position → ℝ) (x : Position)
    (hμ : 0≤μ x) : propagationCoreSource r ‖x‖ (μ x) (initialPropagationError bad r μ x)≤
      4*Real.pi*(if bad then 0 else μ x) := by
  by_cases hb : bad <;> by_cases hd : ‖x‖<r
  all_goals simp [propagationCoreSource,initialPropagationError,hb,hd]
  positivity

lemma initialPropagationOffset_base_weak {bad : Prop} {Z r a : ℝ} {H μ : Position → ℝ}
    (hH : Continuous H) (hμ : LocallyIntegrable μ volume)
    (hw : WeakNuclearSubsolution (fun x => Z*coulombKernel x+H x) Z univ (fun x => 4*Real.pi*μ x)) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+initialPropagationOffset bad Z r a H x) Z univ
      (fun x => 4*Real.pi*(if bad then 0 else μ x)+6*a) := by
  apply (weakNuclearSubsolution_offset_iff (initialPropagationOffset_continuous bad Z r a hH)).2
  have hc : Continuous (fun x => if bad then (0:ℝ) else H x) := by
    by_cases hb : bad <;> simp only [hb,ite_true,ite_false]
    · exact continuous_const
    · exact hH
  have hq : LocallyIntegrable (fun x => 4*Real.pi*(if bad then 0 else μ x)) volume := by
    by_cases hb : bad
    · simp only [ite_eq_left hb,mul_zero]
      exact continuous_const.locallyIntegrable
    · simp only [ite_eq_right hb]
      exact hμ.smul (4*Real.pi)
  have hb : WeakLaplacianGE (fun x => if bad then (0:ℝ) else H x) univ
      (fun x => 4*Real.pi*(if bad then 0 else μ x)) := by
    by_cases hb : bad
    · simpa only [ite_eq_left hb,mul_zero] using WeakLaplacianGE.zero
    · simpa only [ite_eq_right hb] using (weakNuclearSubsolution_offset_iff hH).1 hw
  exact WeakLaplacianGE.add (hc.sub continuous_const)
    (continuous_const.mul (continuous_norm.pow 2)) hq continuous_const.locallyIntegrable
    (hb.sub_const hc ((7/10:ℝ)*Z/r)) (WeakLaplacianGE.quadratic a)

lemma initialPropagationOffset_upper {bad : Prop} {Z r a : ℝ} {H : Position → ℝ}
    (hZ : 0≤Z) (hr : 0<r) (ha : 0≤a) (hquad : 4*a*r^2≤(1/20:ℝ)*Z/r)
    (hH : ∀ x,H x≤0) {x : Position} (hx : r≤‖x‖) (hx' : ‖x‖≤2*r) :
    Z*coulombKernel x+initialPropagationOffset bad Z r a H x≤2*Z/r := by
  have hd := hr.trans_le hx
  have hpot : (if bad then (0:ℝ) else H x)≤0 := by split_ifs; rfl; exact hH x
  have hker : Z*coulombKernel x≤Z/r := by
    change Z*‖x‖⁻¹≤Z/r
    rw [←div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hZ hr hx
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) hx' 2) ha
  unfold initialPropagationOffset
  have hZr : 0≤Z/r := div_nonneg hZ hr.le
  simp only [mul_div_assoc] at hquad ⊢
  nlinarith only [hpot,hker,hsq,hquad,hZr]

lemma initialPropagationOffset_weak {bad : Prop} {Z r a : ℝ} {H μ : Position → ℝ}
    (hZ : 0≤Z) (hr : 0<r) (ha : 0≤a) (hquad : 4*a*r^2≤(1/20:ℝ)*Z/r)
    (hreaction : tfReaction (2*Z/r)≤6*a)
    (hH : Continuous H) (hHnonpos : ∀ x,H x≤0)
    (hμ : Measurable μ) (hμnonneg : ∀ x,0≤μ x)
    (hbμ : ∀ D : ℝ,∃ C : ℝ,∀ x∈Metric.closedBall 0 D,|μ x|≤C)
    (hw : WeakNuclearSubsolution (fun x => Z*coulombKernel x+H x) Z univ (fun x => 4*Real.pi*μ x)) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+initialPropagationOffset bad Z r a H x) Z
      {x | ‖x‖<2*r}
      (fun x => propagationRHS r ‖x‖ (μ x) (initialPropagationError bad r μ x)
        (Z*coulombKernel x+initialPropagationOffset bad Z r a H x)) := by
  have hc := initialPropagationOffset_continuous bad Z r a hH
  have hμi := locallyIntegrable_of_ball_bounds hμ hbμ
  have Hbase := (initialPropagationOffset_base_weak (bad:=bad) (r:=r) (a:=a) hH hμi hw).mono_domain
    (subset_univ {x : Position | ‖x‖<2*r})
  have hqi : LocallyIntegrable (fun x => 4*Real.pi*(if bad then 0 else μ x)+6*a) volume := by
    by_cases hb : bad
    · simpa only [ite_eq_left hb,mul_zero,zero_add] using (continuous_const.locallyIntegrable : LocallyIntegrable (fun _ : Position => 6*a) volume)
    · simp only [ite_eq_right hb]
      have hscaled : LocallyIntegrable (fun x => 4*Real.pi*μ x) volume := hμi.smul (4*Real.pi)
      exact hscaled.add (continuous_const.locallyIntegrable : LocallyIntegrable (fun _ : Position => 6*a) volume)
  apply (weakNuclearSubsolution_offset_iff hc).2
  apply ((weakNuclearSubsolution_offset_iff hc).1 Hbase).mono_source_on hqi
    (propagationRHS_locallyIntegrable hr hc hμ (initialPropagationError_measurable bad r hμ)
      hbμ (initialPropagationError_ball_bounds hbμ))
  exact Eventually.of_forall (fun x hx => by
    have hcore := initial_core_source bad r μ x (hμnonneg x)
    unfold propagationRHS
    by_cases hxr : r≤‖x‖
    · rw [ite_eq_left hxr]
      have hreact := (tfReaction_monotone (initialPropagationOffset_upper (bad:=bad) hZ hr ha hquad hHnonpos hxr
        (le_of_lt hx))).trans hreaction
      exact add_le_add hcore hreact
    · rw [ite_eq_right hxr,add_zero]
      linarith only [hcore,ha])

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma initialPropagationOffset_lower {bad : Prop} {Z r a : ℝ} {H : Position → ℝ}
    (hZ : 0 ≤ Z) (hr : 0<r) (ha : 0 ≤ a)
    (hH : ¬bad → ∀ x,r ≤ ‖x‖ → ‖x‖ ≤ 2*r → -(1/10:ℝ)*Z/r ≤ H x)
    {x : Position} (hx : r ≤ ‖x‖) (hx' : ‖x‖ ≤ (53/50)*r) :
    (7/50:ℝ)*(Z/r) ≤ Z*coulombKernel x+initialPropagationOffset bad Z r a H x := by
  have hd := hr.trans_le hx
  have hpot : -(1/10:ℝ)*(Z/r) ≤ if bad then (0:ℝ) else H x := by
    split_ifs with hb
    · have hh : 0 ≤ Z/r := div_nonneg hZ hr.le
      linarith only [hh]
    · simpa only [mul_div_assoc] using hH hb x hx (by linarith only [hx',hr])
  have hker : (50/53:ℝ)*(Z/r) ≤ Z*coulombKernel x := by
    have hh := div_le_div_of_nonneg_left hZ hd hx'
    change Z/((53/50)*r) ≤ Z/‖x‖ at hh
    change (50/53:ℝ)*(Z/r) ≤ Z*‖x‖⁻¹
    convert hh using 1 <;> field_simp
  have hquad : 0 ≤ a*‖x‖^2 := mul_nonneg ha (sq_nonneg _)
  have hZr := div_nonneg hZ hr.le
  unfold initialPropagationOffset
  simp only [mul_div_assoc]
  linarith only [hpot,hker,hquad,hZr]

lemma initialPropagationOffset_nonpos {bad : Prop} {Z r a : ℝ} {H : Position → ℝ}
    (hZ : 0 ≤ Z) (hr : 0<r) (ha : 0 ≤ a) (hquad : 4*a*r^2 ≤ (1/20:ℝ)*Z/r)
    (hH : ∀ x,H x ≤ 0) {x : Position} (hx : (19/10)*r ≤ ‖x‖) (hx' : ‖x‖ ≤ 2*r) :
    Z*coulombKernel x+initialPropagationOffset bad Z r a H x ≤ 0 := by
  have hd : 0<‖x‖ := (by positivity : (0:ℝ)<(19/10)*r).trans_le hx
  have hpot : (if bad then (0:ℝ) else H x) ≤ 0 := by split_ifs; rfl; exact hH x
  have hker : Z*coulombKernel x ≤ (10/19:ℝ)*(Z/r) := by
    have hh := div_le_div_of_nonneg_left hZ (by positivity : (0:ℝ)<(19/10)*r) hx
    change Z/‖x‖ ≤ Z/((19/10)*r) at hh
    change Z*‖x‖⁻¹ ≤ (10/19:ℝ)*(Z/r)
    convert hh using 1 <;> field_simp
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) hx' 2) ha
  have hZr := div_nonneg hZ hr.le
  unfold initialPropagationOffset
  simp only [mul_div_assoc] at hquad ⊢
  nlinarith only [hpot,hker,hsq,hquad,hZr]

lemma initialPropagationOffset_low_overlap {bad : Prop} {B Z r a : ℝ} {H : Position → ℝ}
    (hB : 0<B) (hZ : 0 ≤ Z) (hr : 0<r) (ha : 0 ≤ a) (hBZ : B ≤ (1/10:ℝ)*Z*r^3)
    (hH : ¬bad → ∀ x,r ≤ ‖x‖ → ‖x‖ ≤ 2*r → -(1/10:ℝ)*Z/r ≤ H x)
    {x : Position} (hx : r ≤ ‖x‖) (hx' : ‖x‖ ≤ (53/50)*r) :
    propagationBarrierOffset B r Z x ≤ initialPropagationOffset bad Z r a H x := by
  have hbar := (propagationBarrier_two_sided hB.le hr hx).2
  have hh : B/‖x‖^4 ≤ B/r^4 := div_le_div_of_nonneg_left hB.le (pow_pos hr 4)
    (pow_le_pow_left₀ hr.le hx 4)
  have hBr : B/r^4 ≤ (1/10:ℝ)*(Z/r) := by
    apply (div_le_iff₀ (pow_pos hr 4)).mpr
    calc
      B ≤ (1/10:ℝ)*Z*r^3 := hBZ
      _ = (1/10:ℝ)*(Z/r)*r^4 := by field_simp
  have hlow := initialPropagationOffset_lower hZ hr ha hH hx hx'
  have hZr := div_nonneg hZ hr.le
  have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hx
  linarith only [hbar,hh,hBr,hlow,hZr,he]

lemma initialPropagationOffset_high_overlap {bad : Prop} {B Z r a : ℝ} {H : Position → ℝ}
    (hB : 0<B) (hZ : 0 ≤ Z) (hr : 0<r) (ha : 0 ≤ a) (hquad : 4*a*r^2 ≤ (1/20:ℝ)*Z/r)
    (hH : ∀ x,H x ≤ 0) {x : Position} (hx : (19/10)*r ≤ ‖x‖) (hx' : ‖x‖ ≤ 2*r) :
    initialPropagationOffset bad Z r a H x ≤ propagationBarrierOffset B r Z x := by
  have hxr : r ≤ ‖x‖ := by linarith only [hx,hr]
  have hp := propagationBarrier_positive hB hr hxr
  have hn := initialPropagationOffset_nonpos (bad:=bad) hZ hr ha hquad hH hx hx'
  have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hxr
  linarith only [hp,hn,he]

def initialNextOffset (bad : Prop) (B Z r a : ℝ) (H : Position → ℝ) : Position → ℝ :=
  radialMaxSplice ((103/100)*r) ((39/20)*r) (initialPropagationOffset bad Z r a H)
    (propagationBarrierOffset B r Z)

lemma initialNextOffset_continuous {bad : Prop} {B Z r a : ℝ} {H : Position → ℝ}
    (hB : 0<B) (hZ : 0 ≤ Z) (hr : 0<r) (ha : 0 ≤ a) (hBZ : B ≤ (1/10:ℝ)*Z*r^3)
    (hquad : 4*a*r^2 ≤ (1/20:ℝ)*Z/r) (hH : Continuous H) (hHnonpos : ∀ x,H x ≤ 0)
    (hHlow : ¬bad → ∀ x,r ≤ ‖x‖ → ‖x‖ ≤ 2*r → -(1/10:ℝ)*Z/r ≤ H x) :
    Continuous (initialNextOffset bad B Z r a H) := by
  apply continuous_radialMaxSplice (a:=(53/50)*r) (b:=r) (e:=(19/10)*r) (c:=2*r)
  · linarith only [hr]
  · linarith only [hr]
  · linarith only [hr]
  · linarith only [hr]
  · linarith only [hr]
  · exact initialPropagationOffset_continuous bad Z r a hH
  · exact propagationBarrierOffset_continuous B Z hr
  · exact fun x hx hx' => initialPropagationOffset_low_overlap hB hZ hr ha hBZ hHlow hx hx'
  · exact fun x hx hx' => initialPropagationOffset_high_overlap hB hZ hr ha hquad hHnonpos hx hx'

end NeutralAtom
end

end

end OAI
