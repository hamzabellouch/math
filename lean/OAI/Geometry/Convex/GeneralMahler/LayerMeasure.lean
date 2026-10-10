import OAI.Geometry.Convex.GeneralMahler.MixedField

namespace OAI
/-! §02 scalar measure from the derivative of avH. Real densities here. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology ENNReal
namespace GeneralMahler

-- A scalar general lemma about finite moments from fast primitive decay.
lemma weighted_primitive_moments_pos (f g F : ℝ → ℝ)
    (h : ∀ x, HasDerivAt f (g x) x) (hn : ∀ x, 0 ≤ g x)
    (c : ℝ) (hv : rapid F) (hmeas : Measurable F)
    (hf : ∀ x : ℝ, 0 < x → f x-c = F x) (n : ℕ) :
    IntegrableOn (fun x => g x*(1+x)^n) (Ioi 0) := by
  let w := fun x:ℝ => (1+x)^n
  let w' := fun x:ℝ => (n:ℝ)*(1+x)^(n-1)
  have hd (x : ℝ) : HasDerivAt w (w' x) x := by
    have he := ((hasDerivAt_id' x).const_add 1).pow n
    change HasDerivAt ((fun x:ℝ=>1+x)^n) _ x
    simpa only [w,w',mul_one] using he
  let v := fun x:ℝ => (f x-c)*w' x
  let P := fun x:ℝ => (f x - c)*w x - ∫ t in (0:ℝ)..x, v t
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (h x).continuousAt
  have hc' : Continuous v := by unfold v w'; fun_prop
  have hp (x:ℝ) : HasDerivAt P (g x*w x) x := by
    have hb := (((h x).sub_const c).mul (hd x)).sub (intervalIntegral.integral_hasDerivAt_right
      (hc'.intervalIntegrable (0:ℝ) x)
      (hc'.stronglyMeasurableAtFilter volume (𝓝 x)) hc'.continuousAt)
    convert hb using 1
    all_goals first | rfl | (unfold v; ring)
  have hw : PolyBound (fun x:ℝ => 1+x) :=
    (PolyBound.const 1).add PolyBound.id
  have hi := (hv.product ((PolyBound.const (n:ℝ)).mul (hw.pow (n-1)))).integrable_real
    (hmeas.mul (by fun_prop))
  have hii : IntegrableOn v (Ioi 0) :=
    hi.integrableOn.congr_fun (by intro x hx; simp [v,w',hf x hx]) measurableSet_Ioi
  have he := intervalIntegral_tendsto_integral_Ioi 0 hii tendsto_id
  have he' : Tendsto (fun x => (f x-c)*w x) atTop (𝓝 0) := by
    apply Tendsto.congr' _ (hv.product (hw.pow n)).tail_limit
    filter_upwards [Ioi_mem_atTop (0:ℝ)] with x hx
    rw [hf x hx]
  apply integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hp x) (fun x hx => ?_) (he'.sub he)
  exact mul_nonneg (hn _) (pow_nonneg (by have ha : 0 < x := hx; linarith) _)

open Layers
variable {m : ℕ} [NeZero m]
namespace ProjField
variable (q : ProjField m)

def layerW (z : ℝ) := p z * q.Bt z + a z * q.r1 z
omit [NeZero m] in
lemma H_deriv (z : ℝ) : HasDerivAt q.avH (q.layerW z) z := q.deriv_avH z
omit [NeZero m] in
lemma H_cont : Continuous q.avH :=
  continuous_iff_continuousAt.mpr fun x => (q.H_deriv x).continuousAt
omit [NeZero m] in
lemma w_cont : Continuous q.layerW :=
  (cp.mul q.Bt_cd.continuous).add (ca.mul q.Bt_cd.continuous_deriv_one.neg)
lemma w_positive (z : ℝ) : 0 < q.layerW z :=
  add_pos_of_nonneg_of_pos (mul_nonneg (p_pos z).le (q.Bt_nonneg z)) (mul_pos (a_pos z) (q.r1_pos z))

lemma H_infty : Tendsto q.avH atTop (𝓝 q.s0) := by
  have he := (q.tail_H.tail_limit).add_const q.s0
  rw [zero_add] at he
  apply Tendsto.congr' _ he
  filter_upwards [Ioi_mem_atTop (0:ℝ)] with x hx

  simp [st,(le_of_lt (show 0<x from hx))]

lemma H_bot : Tendsto q.avH atBot (𝓝 0) := by
  have h : rapid (fun x : ℝ => q.avH (-x)-st (-x)*q.s0) := by
    intro n
    obtain ⟨C,hc,h⟩ := q.tail_H n
    exact ⟨C,hc,fun x => by simpa only [norm_neg] using h (-x)⟩
  have he : Tendsto (fun x:ℝ => q.avH (-x)) atTop (𝓝 0) := by
    apply Tendsto.congr' _ h.tail_limit
    filter_upwards [Ioi_mem_atTop (0:ℝ)] with x hx

    simp [st,show ¬0 ≤ -x by have ha : 0 < x := hx; linarith]
  simpa [Function.comp_def] using he.comp tendsto_neg_atBot_atTop

theorem w_moment (n : ℕ) :
    Integrable (fun x => q.layerW x * (1+‖x‖)^n) := by
  let f := fun x => q.avH x-st x*q.s0
  have hm : Measurable f := q.H_cont.measurable.sub (measurable_st.mul measurable_const)
  let w := fun x => q.layerW x * (1+‖x‖)^n
  have hp : IntegrableOn w (Ioi 0) := by
    have h := weighted_primitive_moments_pos q.avH q.layerW f q.H_deriv (fun x =>
      (q.w_positive x).le) q.s0 q.tail_H hm (fun x hx => by simp [f,st,hx.le]) n
    exact h.congr_fun (fun x hx => by simp only [w,Real.norm_of_nonneg (mem_Ioi.mp hx).le])
      measurableSet_Ioi
  have hn : IntegrableOn w (Iio 0) := by
    let F := fun x:ℝ => -f (-x)
    have he : rapid F := by
      intro n
      obtain ⟨C,hc,h⟩ := q.tail_H n
      exact ⟨C,hc,fun x=>by simpa only [F,f,norm_neg] using h (-x)⟩
    have h := weighted_primitive_moments_pos (fun x => -q.avH (-x))
      (fun x => q.layerW (-x)) F (fun x => by
        change HasDerivAt (- (q.avH ∘ (fun x => -x))) _ _
        simpa using ((q.H_deriv (-x)).comp x (hasDerivAt_neg' x)).neg) (fun x =>
      (q.w_positive _).le) 0 he (hm.neg.comp measurable_neg)
      (fun x hx => by simp [F,f,st,not_le_of_gt hx]) n
    have h₁ : IntegrableOn (w ∘ (fun t=> -t)) ((fun t : ℝ=> -t) ⁻¹' Iio (0:ℝ)) ↔ IntegrableOn w (Iio 0) :=
      MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _)
        (Homeomorph.neg ℝ).measurableEmbedding
    apply h₁.mp
    have heq : (fun x : ℝ=> -x) ⁻¹' Iio (0:ℝ) = Ioi 0 := by ext; simp
    rw [heq]
    exact h.congr_fun (by intro x hx; simp [w,abs_of_nonneg (mem_Ioi.mp hx).le])
      measurableSet_Ioi
  have hw : IntegrableOn w (Iic 0) := (integrableOn_Iic_iff_integrableOn_Iio (by finiteness)).mpr hn
  have h := hw.union hp
  rw [Iic_union_Ioi,integrableOn_univ] at h; exact h
theorem integrable_w : Integrable q.layerW := by simpa using q.w_moment 0
theorem integral_w : ∫ x, q.layerW x = q.s0 := by
  simpa using integral_of_hasDerivAt_of_tendsto q.H_deriv q.integrable_w q.H_bot q.H_infty

end ProjField
end GeneralMahler

end

end OAI
