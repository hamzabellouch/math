import OAI.Geometry.Convex.GeneralMahler.pRapid

namespace OAI
/-! §03 scalar log-Jacobian weights. Antitonicity of W via an
elementary argument that integration from -∞ preserves log concavity. -/
noncomputable section
open MeasureTheory Set Real Filter Metric
open scoped Topology NNReal ENNReal
namespace GeneralMahler
namespace rapid
lemma tail_limit_bot {f:ℝ→ℝ} (hf:rapid f) :
    Tendsto f atBot (𝓝 0) := by
  have h : rapid fun x:ℝ=>f (-x) := by
    intro n
    obtain ⟨C,hc,he⟩ := hf n
    exact ⟨C,hc,fun x=>by simpa using he (-x)⟩
  simpa [Function.comp_def] using h.tail_limit.comp tendsto_neg_atBot_atTop
end rapid
namespace Layers

lemma pbot : Tendsto p atBot (𝓝 0) := by
  apply Tendsto.congr' _ rapid_p.tail_limit_bot
  filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
  simp [st,hx]
lemma ptop : Tendsto p atTop (𝓝 1) := by
  have h := pbot.comp tendsto_neg_atTop_atBot
  have he : Tendsto (fun x:ℝ=>1-(p∘fun x:ℝ=>-x) x) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub h (a := (1:ℝ))
  simpa [Function.comp_def,neg_p] using he

lemma abot (g:ℝ→ℝ) (h : PolyBound g) :
    Tendsto (fun z=>a z*g z) atBot (𝓝 0) := by
  have h₁ := (rapid_phi.product h).tail_limit_bot
  have h₂ := (rapid_p.product (PolyBound.id.mul h)).tail_limit_bot
  have h := h₁.add h₂; rw [zero_add] at h
  apply Tendsto.congr' _ h
  filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
  simp [st,not_le_of_gt hx,a]; ring
lemma abot' : Tendsto a atBot (𝓝 0) := by
  simpa using abot _ (PolyBound.const 1)

def MillsC (x : ℝ) := phi x/p x
def MillsJ (x : ℝ) := x+MillsC x
def MillsW (x : ℝ) := MillsJ x*MillsC x

lemma mc_pos (x:ℝ) : 0 < MillsC x := div_pos (phi_pos _) (p_pos _)
lemma mj_eq (x:ℝ) : MillsJ x = a x/p x := by
  have hp := (p_pos x)
  unfold a MillsJ MillsC
  field_simp
  ring
lemma mj_pos (x : ℝ) : 0 < MillsJ x := by rw [mj_eq]; exact div_pos (a_pos _) (p_pos _)
lemma mw_pos (x : ℝ) : 0 < MillsW x := mul_pos (mj_pos _) (mc_pos _)

lemma d_mc (x : ℝ) : HasDerivAt MillsC (-MillsW x) x := by
  convert (d_phi x).div (d_p x) (p_pos x).ne' using 1
  all_goals first | rfl | (simp only [MillsW,MillsC,MillsJ]; have h:=p_pos x; field_simp; ring)
lemma d_mj (x:ℝ) : HasDerivAt MillsJ (1-MillsW x) x := by
  rw [sub_eq_add_neg]
  exact (hasDerivAt_id' x).add (d_mc x)
lemma d_mw (x:ℝ) : HasDerivAt MillsW (MillsC x*((1-MillsW x)-MillsJ x^2)) x := by
  convert (d_mj x).mul (d_mc x) using 1
  all_goals first | rfl | (unfold MillsW; ring)

lemma c_mc : Continuous MillsC := continuous_iff_continuousAt.mpr fun x => (d_mc x).continuousAt
lemma c_mj : Continuous MillsJ := continuous_iff_continuousAt.mpr fun x => (d_mj x).continuousAt
lemma c_mw : Continuous MillsW := continuous_iff_continuousAt.mpr fun x => (d_mw x).continuousAt
lemma mc_anti : StrictAnti MillsC :=
  strictAnti_of_deriv_neg (fun x=>by rw [(d_mc x).deriv]; exact neg_lt_zero.mpr (mw_pos _))

-- log-concavity of p implies that of its primitive a and again of ∫a
lemma mw_le (x:ℝ) : MillsW x ≤ 1 := by
  let f := fun y=> p y-MillsC x*a y
  have hd (y) : HasDerivAt f (phi y-MillsC x*p y) y := (d_p y).sub ((d_a y).const_mul _)
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun y=> (hd y).continuousAt
  have h : MonotoneOn f (Iic x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic _) hc.continuousOn
      (fun y _=> (hd y).differentiableAt.differentiableWithinAt)
    intro y hy
    have hy' : y≤x := mem_Iic.mp (interior_subset hy)
    rw [(hd y).deriv]
    have hi := mc_anti.antitone hy'
    change MillsC x ≤ phi y/p y at hi
    rw [le_div_iff₀ (p_pos _)] at hi
    linarith
  have hi : Tendsto f atBot (𝓝 0) := by
    have he := pbot.sub (abot'.const_mul (MillsC x))
    simpa [f] using he
  have hh : 0 ≤ f x := le_of_tendsto hi (by filter_upwards [eventually_le_atBot x] with y hy; exact h hy (mem_Iic.mpr (le_refl _)) hy)
  change 0 ≤ _-_ at hh
  rw [MillsW, mj_eq, div_mul_eq_mul_div, div_le_iff₀ (p_pos x)]
  linarith
lemma mj_mono : Monotone MillsJ := by
  apply monotone_of_deriv_nonneg
  · exact fun x=> (d_mj x).differentiableAt
  intro x; rw [(d_mj x).deriv]; linarith [mw_le x]
lemma mw_anti : Antitone MillsW := by
  apply antitone_of_deriv_nonpos (fun x=> (d_mw x).differentiableAt)
  intro x
  let b := fun y=> (p y + y*a y)/2
  have hb (y) : HasDerivAt b (a y) y := by
    convert ((d_p y).add ((hasDerivAt_id' y).mul (d_a y))).div_const 2 using 1
    all_goals first | rfl | (simp only [one_mul,a]; ring)
  let f := fun y=> MillsJ x*a y - b y
  have hd (y) : HasDerivAt f (MillsJ x*p y - a y) y :=
    ((d_a y).const_mul _).sub (hb y)
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun y=> (hd y).continuousAt
  have h : MonotoneOn f (Iic x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic _) hc.continuousOn
      (fun y _=> (hd y).differentiableAt.differentiableWithinAt)
    intro y hy
    have hy' : y≤x := mem_Iic.mp (interior_subset hy)
    rw [(hd y).deriv]
    have hi := mj_mono hy'
    rw [mj_eq y,div_le_iff₀ (p_pos _)] at hi
    linarith
  have hu : Tendsto b atBot (𝓝 0) := by
    have hv := (pbot.add (abot _ PolyBound.id)).div_const 2
    simpa [b,mul_comm] using hv
  have hi : Tendsto f atBot (𝓝 0) := by simpa [f] using (abot'.const_mul (MillsJ x)).sub hu
  have hh : 0 ≤ f x := le_of_tendsto hi (by filter_upwards [eventually_le_atBot x] with y hy; exact h hy (mem_Iic.mpr (le_refl _)) hy)
  rw [(d_mw x).deriv]
  apply mul_nonpos_of_nonneg_of_nonpos (mc_pos _).le
  change 0 ≤ MillsJ x*a x-(p x+x*a x)/2 at hh
  unfold MillsW
  rw [mj_eq]; rw [mj_eq] at hh
  unfold MillsC
  have hl := p_pos x
  field_simp at hh ⊢
  have he : a x=phi x+x*p x := rfl
  rw [show phi x=a x-x*p x from by linarith]
  nlinarith

lemma mc_lip : LipschitzWith 1 MillsC := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact fun x=> (d_mc x).differentiableAt
  intro x
  rw [(d_mc x).deriv,nnnorm_neg]

  apply NNReal.coe_le_coe.mp
  simpa [Real.norm_of_nonneg (mw_pos x).le] using mw_le x
lemma poly_mc : PolyBound MillsC := PolyBound.lipschitz mc_lip
lemma poly_mj : PolyBound MillsJ := PolyBound.id.add poly_mc
lemma poly_mw : PolyBound MillsW := poly_mj.mul poly_mc

lemma rapid_mcs : rapid (fun x=> MillsC x * st x) := by
  apply (rapid_phi.product (PolyBound.const (2:ℝ))).mono
  intro x
  unfold st; split_ifs with hx
  · rw [mul_one,Real.norm_of_nonneg (mc_pos _).le,
      Real.norm_of_nonneg (mul_nonneg (phi_pos x).le (by norm_num))]
    have hh := p_mono.monotone hx
    rw [p_half] at hh
    unfold MillsC
    rw [div_le_iff₀ (p_pos x)]
    nlinarith [phi_pos x]
  simp
lemma rapid_mws : rapid (fun x=> MillsW x * st x) := by
  convert rapid_mcs.product poly_mj using 1
  ext x; unfold MillsW; ring

lemma limit_mc : Tendsto MillsC atTop (𝓝 0) := by
  have h := rapid_phi.tail_limit.div ptop one_ne_zero
  rw [zero_div] at h; exact h

lemma mw_tail (x:ℝ) : IntegrableOn MillsW (Ioi x) ∧
    (∫ z in Ioi x, MillsW z)=MillsC x := by
  have he (x:ℝ) : HasDerivAt (-MillsC) (MillsW x) x := by simpa using (d_mc x).neg
  have h : Tendsto (-MillsC) atTop (𝓝 0) := by have h:= limit_mc.neg; rw [neg_zero] at h; exact h
  have hi := integrableOn_Ioi_deriv_of_nonneg' (a:=x) (fun z _=>he z) (fun z _=>(mw_pos z).le) h
  refine ⟨hi,?_⟩
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (fun z _=>he z) hi h
end Layers
end GeneralMahler

end

end OAI
