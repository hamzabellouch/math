import OAI.Geometry.Convex.GeneralMahler.Qprimitive

namespace OAI
/-! Inverse-kernel and variation identity Eq14. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler
open Profile Layers
def Nr (g:ℝ→ℝ) := fun x=> g x+N g x
lemma nr_test {f:ℝ→ℝ} (hf:TestF f) : TestF (Nr f) :=
  hf.add ((TestF.id.mul hf.der).sub hf.der.der)

namespace rightLayer
lemma std_hb : rapid fun x=> a (-x)*st x := rapid_ar
lemma Qpos_id (x:ℝ) : p x*a (-x)+a x*p (-x)=phi x := by
  rw [neg_p]; exact ProjField.a0_id _

def stdL : rightLayer where
  r := fun x=>p (-x)
  B := fun x=>a (-x)
  hr := fun x=> (p_pos _).le
  hc := cp.comp continuous_neg
  drB := fun x=> by
    convert (d_a (-x)).comp x (hasDerivAt_neg' x) using 1
    all_goals first | rfl | ring
  hb := std_hb
  poly := poly_a.comp PolyBound.id.neg
  hw := by
    simp_rw [Qpos_id]; exact MomentF.of_rapid rapid_phi c_phi.measurable

lemma Ileft {f:ℝ→ℝ} (hf:TestF f) (x:ℝ) :
    IntegrableOn (fun t=>p t*f t) (Iic x) := by
  have h : IntegrableOn (fun t=>p t*f t) (Iio 0) := by
    have hi := ((rapid_p.product hf.poly).integrable_real
      ((cp.measurable.sub measurable_st).mul hf.cont.measurable))
    exact hi.integrableOn.congr_fun (fun t ht=>by
      unfold st; simp [not_le_of_gt (mem_Iio.mp ht)]) measurableSet_Iio
  exact ((h.union (cp.mul hf.cont).integrableOn_Icc).mono_set
    (show Iic x ⊆ Iio 0 ∪ Icc 0 x from fun y hy=> by
      rcases lt_or_ge y 0 with h|h
      · exact Or.inl h
      exact Or.inr ⟨h,mem_Iic.mp hy⟩))

lemma pleft {b:ℝ→ℝ} (hb:TestF b) (x:ℝ) :
    (∫ y in Iic x,p y*Nr b y)=a x*b x-p x*deriv b x := by
  let F := fun x=> a x*b x-p x*deriv b x
  have hd (x:ℝ) : HasDerivAt F (p x*Nr b x) x := by
    convert (((d_a x).fun_mul (hb.diff x).hasDerivAt).fun_sub
      ((d_p x).fun_mul (hb.der.diff x).hasDerivAt)) using 1
    all_goals first | rfl | (unfold Nr N a; ring)
  have hl : Tendsto F atBot (𝓝 0) := by
    have h₂ : Tendsto (fun x=>p x*deriv b x) atBot (𝓝 0) := by
      apply Tendsto.congr' _ (rapid_p.product hb.der.poly).tail_limit_bot
      filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx; simp [st,not_le_of_gt hx]
    simpa [F] using ((abot _ hb.poly).sub h₂)
  have hi := integral_Iic_of_hasDerivAt_of_tendsto'
    (fun x _=>hd x) (Ileft (nr_test hb) x) hl
  simpa [F] using hi

lemma right_i {b:ℝ→ℝ} (hb:TestF b) (x:ℝ) :
    IntegrableOn (fun t=> p (-t)*b t) (Ioi x) := by
  let l := (Homeomorph.neg ℝ)
  have h := Ileft hb.ref (-x)
  have hv := ((Measure.measurePreserving_neg volume).integrableOn_comp_preimage
    l.measurableEmbedding).mpr h
  have he : (fun t:ℝ=> -t) ⁻¹' Iic (-x)=Ici x := by ext; simp
  rw [he] at hv
  simp only [Function.comp_def,neg_neg] at hv
  exact hv.mono_set Ioi_subset_Ici_self

lemma pright {b} (hb:TestF b) (x:ℝ) :
    (∫ y in Ioi x,p (-y)*Nr b y)=a (-x)*b x+p (-x)*deriv b x := by
  let F := fun t=> -(a (-t)*b t+p (-t)*deriv b t)
  have hd (x:ℝ) : HasDerivAt F (p (-x)*Nr b x) x := by
    convert (((((d_a (-x)).comp x (hasDerivAt_neg' x)).fun_mul
      (hb.diff x).hasDerivAt).fun_add (((d_p (-x)).comp x (hasDerivAt_neg' x)).fun_mul
        (hb.der.diff x).hasDerivAt)).neg) using 1
    all_goals first | rfl | (simp only [Function.comp_apply]; unfold Nr N a; ring)
  have hl : Tendsto F atTop (𝓝 0) := by
    have h₁ := (std_hb.product hb.poly).tail_limit
    have h₂ := (rapid_p.product hb.der.ref.poly).tail_limit_bot.comp tendsto_neg_atTop_atBot
    have hh : Tendsto (fun t=> -(a (-t)*st t*b t+(p (-t)-st (-t))*deriv b t)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (h₁.add h₂).neg
    apply Tendsto.congr' _ hh
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; simp [F,st,hx.le,hx]
  simpa [F] using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _=>hd x) (right_i (nr_test hb) x) hl

lemma Q0_cov {b f} (hb:TestF b) (hf:TestF f) :
    stdL.Q f (Nr b) = ga (fun x=>f x*b x) := by
  unfold Q
  rw [show (volume:Measure Plane)=volume.prod volume from rfl]
  rw [integral_prod _ (stdL.Q_int hf (nr_test hb))]
  unfold ga; congr 1; ext x
  classical
  let g := (Iic x).indicator fun y=> (p y*Nr b y)*(f x*p (-x))
  let h := (Ioi x).indicator fun y=> (p (-y)*Nr b y)*(f x*p x)
  have he : (fun y=>stdL.Km (x,y)*(f x*Nr b y))=fun y=>g y+h y := by
    ext y; rcases le_or_gt y x with hx|hx
    · simp [g,h,Km,stdL,hx, not_lt_of_ge hx]; ring
    simp [g,h,Km,stdL,hx,hx.le,not_le_of_gt hx]; ring
  rw [he,integral_add]
  · unfold g h; rw [integral_indicator measurableSet_Iic,integral_indicator measurableSet_Ioi,
      integral_mul_const,integral_mul_const,pleft hb,pright hb,← Qpos_id x]; ring
  · exact (integrable_indicator_iff measurableSet_Iic).mpr ((Ileft (nr_test hb) x).mul_const _)
  exact (integrable_indicator_iff measurableSet_Ioi).mpr ((right_i (nr_test hb) x).mul_const _)

variable (q:rightLayer)
lemma arM : MomentF fun x=>a x*q.r x :=
  q.hw.mono (ca.mul q.hc).measurable (fun x=>by
    have he : 0 ≤ q.B x := by rw [← (q.r_slice x).2]; exact integral_nonneg q.hr
    have h : 0 ≤ p x*q.B x := mul_nonneg (p_pos x).le he
    have hh := mul_nonneg (a_pos x).le (q.hr x)
    change ‖a x*q.r x‖≤‖p x*q.B x+a x*q.r x‖
    rw [Real.norm_of_nonneg hh,Real.norm_of_nonneg (by positivity)]; linarith)
lemma prM : MomentF fun x=>p x*q.r x := by
  have h := q.arM.mul ratio_bound (cp.measurable.div ca.measurable)
  convert h using 1
  ext x; field_simp [ne_of_gt (a_pos x)]

def variationK (r:ℝ→ℝ) (b c:ℝ→ℝ) (x:ℝ) :=
  (a x*r x)*(Nr b x*c x) - (p x*r x)*(Nr b x*deriv c x)
lemma varI {b c r} (hr:MomentF fun x=>a x*r x) (hp:MomentF fun x=>p x*r x)
    (hb:TestF b) (hc:TestF c) :
    Integrable (variationK r b c) :=
  (hr.int_test ((nr_test hb).mul hc)).sub (hp.int_test ((nr_test hb).mul hc.der))
lemma Q_var {b c} (hb:TestF b) (hc:TestF c) :
    q.Q (Nr b) (Nr c)=(∫ x,variationK q.r c b x)+(∫ x,variationK q.r b c x) := by
  rw [q.Q_split (nr_test hb) (nr_test hc)]
  have hi (b c:ℝ→ℝ) (hb:TestF b) :
      (fun x=> q.r x*Nr c x*∫ y in Iio x,p y*Nr b y)=fun x=>variationK q.r c b x := by
    ext x; rw [← integral_Iic_eq_integral_Iio,pleft hb]; unfold variationK; ring
  rw [hi b c hb, hi c b hc]
end rightLayer
end GeneralMahler

end

end OAI
