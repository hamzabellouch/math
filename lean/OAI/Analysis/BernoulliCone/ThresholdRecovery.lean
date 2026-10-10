import OAI.Analysis.BernoulliCone.LowerComparison

namespace OAI

universe uα uF

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Bernoulli.ThresholdRecovery

section L2
variable {α : Type uα} {F : Type uF} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma integral_norm_sq_eq {f : α → F} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

lemma tendsto_integral_norm_sq {f : ℕ → α → F} {g : α → F}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hc : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖f n x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x, ‖g x‖ ^ 2 ∂μ)) := by
  have ht : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
    apply tendsto_iff_enorm_sub_tendsto_zero.mpr
    simpa only [← MemLp.toLp_sub, Lp.enorm_toLp] using hc
  have hi (n : ℕ) := integral_norm_sq_eq (hf n)
  simp_rw [hi, integral_norm_sq_eq hg]
  exact ht.norm.pow 2

end L2

def ramp (ε t:ℝ) : ℝ := min (max (t/ε) 0) 1
lemma ramp_continuous (ε:ℝ) : Continuous (ramp ε) := by
  unfold ramp
  fun_prop
lemma ramp_nonneg (ε t:ℝ) : 0≤ramp ε t := le_min (le_max_right _ _) zero_le_one
lemma ramp_le_one (ε t:ℝ) : ramp ε t≤1 := min_le_right _ _
lemma ramp_norm_le (ε t:ℝ) : ‖ramp ε t‖≤1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (ramp_nonneg _ _)]
  exact ramp_le_one _ _
def envelope (ε u w:ℝ) : ℝ := if 0<u then 1 else ramp ε w
lemma envelope_norm_le (ε u w:ℝ) : ‖envelope ε u w‖≤1 := by
  unfold envelope
  split_ifs
  · norm_num
  · exact ramp_norm_le _ _
lemma phase_threshold_le {ε u w:ℝ} (hε:0<ε) (hu:0≤u) :
    (if 0<u+max (w-ε) 0 then (1:ℝ) else 0)≤envelope ε u w := by
  by_cases hup:0<u
  · rw [envelope,ite_eq_left hup]
    split_ifs <;> norm_num
  · have hu0:u=0:=le_antisymm (not_lt.mp hup) hu
    subst u
    rw [envelope,ite_eq_right (lt_irrefl _)]
    by_cases hw:ε<w
    · have hdiv:1<w/ε:=(lt_div_iff₀ hε).mpr (by simpa using hw)
      simp only [ramp,max_eq_left (by linarith : 0≤w/ε),min_eq_right hdiv.le]
      split_ifs <;> norm_num
    · have he:w-ε≤0:=sub_nonpos.mpr (not_lt.mp hw)
      simp only [max_eq_right he,add_zero,lt_self_iff_false,ite_false]
      exact ramp_nonneg _ _
lemma envelope_le_phase {ε u w:ℝ} (_hε:0<ε) (hu:0≤u) (hw:0≤w) :
    envelope ε u w≤(if 0<u+w then (1:ℝ) else 0) := by
  by_cases hup:0<u
  · simp only [envelope,ite_eq_left hup,ite_eq_left (by linarith : 0<u+w),le_refl]
  · rw [envelope,ite_eq_right hup]
    by_cases hsum:0<u+w
    · rw [ite_eq_left hsum]; exact ramp_le_one _ _
    · have hw0:w=0:=by linarith
      simp [hw0,hup,ramp]
section Integrals
variable {α : Type uα} [MeasurableSpace α] {μ:Measure α} [IsFiniteMeasure μ]
omit [IsFiniteMeasure μ] in
lemma envelope_measurable {u w:α→ℝ} (hu:AEStronglyMeasurable u μ)
    (hw:AEStronglyMeasurable w μ) (ε:ℝ) :
    AEStronglyMeasurable (fun x=>envelope ε (u x) (w x)) μ := by
  have hm:Measurable (fun p:ℝ×ℝ=>envelope ε p.1 p.2) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_const
      ((ramp_continuous ε).measurable.comp measurable_snd)
  exact (hm.comp_aemeasurable (hu.aemeasurable.prodMk hw.aemeasurable)).aestronglyMeasurable
lemma envelope_integrable {u w:α→ℝ} (hu:AEStronglyMeasurable u μ)
    (hw:AEStronglyMeasurable w μ) (ε:ℝ) :
    Integrable (fun x=>envelope ε (u x) (w x)) μ :=
  (integrable_const (1:ℝ)).mono' (envelope_measurable hu hw ε)
    (Eventually.of_forall fun _=>envelope_norm_le _ _ _)
lemma envelope_integral_tendsto {u w:α→ℝ} {f:ℕ→α→ℝ}
    (hu:AEStronglyMeasurable u μ) (hf:∀n,AEStronglyMeasurable (f n) μ)
    (hp:∀ᵐ x ∂μ,Tendsto (fun n=>f n x) atTop (𝓝 (w x))) (ε:ℝ) :
    Tendsto (fun n=>∫x,envelope ε (u x) (f n x) ∂μ) atTop
      (𝓝 (∫x,envelope ε (u x) (w x) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _=>1)
  · exact fun n=>envelope_measurable hu (hf n) ε
  · exact integrable_const _
  · exact fun _=>Eventually.of_forall fun _=>envelope_norm_le _ _ _
  · filter_upwards [hp] with x hx
    by_cases hu':0<u x
    · simp only [envelope,ite_eq_left hu']; exact tendsto_const_nhds
    · simp only [envelope,ite_eq_right hu']
      exact ((ramp_continuous ε).tendsto (w x)).comp hx
end Integrals

variable {d:ℕ}
lemma h1_const_ball (c:Space d) (r a:ℝ) :
    H1 (Metric.ball c r) (fun _=>a) (fun _=>0) := by
  simpa only [gradient_fun_const',Pi.zero_apply] using (LipschitzSobolev.h1_ball (LipschitzWith.const a) c r)
lemma h1_sub_const_ball {c:Space d} {r:ℝ} {u:Space d→ℝ} {G:Space d→Space d}
    (hu:H1 (Metric.ball c r) u G) (a:ℝ) :
    H1 (Metric.ball c r) (fun x=>u x-a) G := by
  simpa only [sub_zero] using hu.sub (h1_const_ball c r a)
/-- Strong H1-density gives the exact upper comparison after fixed positive
threshold truncation. The discontinuous phase term is controlled by a continuous
ramp, not by an unjustified continuity assertion for positivity sets. -/
lemma fixed_threshold_limit {c:Space d} {r:ℝ} {u w:Space d→ℝ}
    {G W:Space d→Space d} (hu:H1 (Metric.ball c r) u G)
    (hw:H10 (Metric.ball c r) w W)
    (hun:∀ᵐ x ∂volume.restrict (Metric.ball c r),0≤u x)
    (hwn:∀ᵐ x ∂volume.restrict (Metric.ball c r),0≤w x)
    {ε:ℝ} (hε:0<ε)
    (hcomp:∀φ:Space d→ℝ,Test (Metric.ball c r) φ →
      energy (Metric.ball c r) u G≤energy (Metric.ball c r)
        (fun x=>u x+max (φ x-ε) 0)
        (fun x=>G x+(if 0<φ x-ε then (1:ℝ) else 0) • gradient φ x)) :
    energy (Metric.ball c r) u G≤
      (∫x in Metric.ball c r,‖G x+(if 0<w x-ε then (1:ℝ) else 0) • W x‖^2)+
      (∫x in Metric.ball c r,if 0<u x+w x then (1:ℝ) else 0) := by
  let B:=Metric.ball c r
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨f,hf,hfw,hfW⟩:=SobolevCalculus.H10_sequence hw
  obtain ⟨ns,hns,hpoint⟩:=(tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (2:ℝ≥0∞)≠0) hfw).exists_seq_tendsto_ae
  let F:ℕ→Space d→Space d:=fun n x=>G x+(if 0<f (ns n) x-ε then (1:ℝ) else 0) • gradient (f (ns n)) x
  let V:Space d→Space d:=fun x=>G x+(if 0<w x-ε then (1:ℝ) else 0) • W x
  have hs (n:ℕ):H1 B (fun x=>max (f (ns n) x-ε) 0)
      (fun x=>(if 0<f (ns n) x-ε then (1:ℝ) else 0) • gradient (f (ns n)) x):=
    SobolevCalculus.h1_positivePart Metric.isOpen_ball (h1_sub_const_ball (hf (ns n)).h1 ε)
  have hV:H1 B (fun x=>u x+max (w x-ε) 0) V :=
    hu.add (SobolevCalculus.h1_positivePart Metric.isOpen_ball (h1_sub_const_ball hw.1 ε))
  have hF(n:ℕ):H1 B (fun x=>u x+max (f (ns n) x-ε) 0) (F n):=hu.add (hs n)
  have hstrong:Tendsto (fun n=>eLpNorm (F n-V) 2 (volume.restrict B)) atTop (𝓝 0) := by
    have hp:∀ᵐ x ∂volume.restrict B,Tendsto (fun n=>f (ns n) x-ε) atTop (𝓝 (w x-ε)):=by
      filter_upwards [hpoint] with x hx
      exact hx.sub_const ε
    have hh:=SobolevCalculus.positivePart_gradient_strong_of_ae Metric.isOpen_ball
      (h1_sub_const_ball hw.1 ε) (fun n=>h1_sub_const_ball (hf (ns n)).h1 ε) hp
      (hfW.comp hns.tendsto_atTop)
    convert hh using 1
    funext n
    congr 1
    funext x
    dsimp [F,V]
    abel
  have hlim:=tendsto_integral_norm_sq (fun n=>(hF n).2.1) hV.2.1 hstrong
  have henv:=envelope_integral_tendsto hu.1.aestronglyMeasurable
    (fun n=>(hf (ns n)).h1.1.aestronglyMeasurable) hpoint ε
  have hbound(n:ℕ):energy B u G≤(∫x in B,‖F n x‖^2)+
      (∫x in B,envelope ε (u x) (f (ns n) x)) := by
    apply (hcomp _ (hf (ns n))).trans
    rw [energy,integral_add ((hF n).2.1.integrable_norm_pow (by norm_num))
      (integrable_phase (hF n).1.aestronglyMeasurable)]
    apply add_le_add le_rfl
    apply integral_mono_ae (integrable_phase (hF n).1.aestronglyMeasurable)
      (envelope_integrable hu.1.aestronglyMeasurable (hf (ns n)).h1.1.aestronglyMeasurable ε)
    filter_upwards [hun] with x hx
    exact phase_threshold_le hε hx
  have hh:=ge_of_tendsto (hlim.add henv) (Eventually.of_forall hbound)
  apply hh.trans
  apply add_le_add le_rfl
  apply integral_mono_ae (envelope_integrable hu.1.aestronglyMeasurable hw.1.1.aestronglyMeasurable ε)
    (integrable_phase (hu.add hw.1).1.aestronglyMeasurable)
  filter_upwards [hun,hwn] with x hx hwx
  exact envelope_le_phase hε hx hwx
/-- The faithful arbitrary-Sobolev upper-variation bridge. The sole comparison
input here is the concrete thresholded compact-test inequality; all density and
phase-limit steps are proved, without regularity assumptions on the competitor. -/
theorem upper_variation_of_threshold_tests {c:Space d} {r:ℝ} {u w:Space d→ℝ}
    {G W:Space d→Space d} (hu:H1 (Metric.ball c r) u G)
    (hw:H10 (Metric.ball c r) w W)
    (hun:∀ᵐ x ∂volume.restrict (Metric.ball c r),0≤u x)
    (hwn:∀ᵐ x ∂volume.restrict (Metric.ball c r),0≤w x)
    (hcomp:∀ε:ℝ,0<ε → ∀φ:Space d→ℝ,Test (Metric.ball c r) φ →
      energy (Metric.ball c r) u G≤energy (Metric.ball c r)
        (fun x=>u x+max (φ x-ε) 0)
        (fun x=>G x+(if 0<φ x-ε then (1:ℝ) else 0) • gradient φ x)) :
    energy (Metric.ball c r) u G≤energy (Metric.ball c r)
      (fun x=>u x+w x) (fun x=>G x+W x) := by
  let B:=Metric.ball c r
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let ε:ℕ→ℝ:=fun n=>1/((n:ℝ)+1)
  have hε(n:ℕ):0<ε n:=by dsimp [ε]; positivity
  have hεlim:Tendsto ε atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  let F:ℕ→Space d→Space d:=fun n x=>G x+(if 0<w x-ε n then (1:ℝ) else 0) • W x
  let V:Space d→Space d:=fun x=>G x+(if 0<w x then (1:ℝ) else 0) • W x
  have hF(n:ℕ):H1 B (fun x=>u x+max (w x-ε n) 0) (F n):=
    hu.add (SobolevCalculus.h1_positivePart Metric.isOpen_ball (h1_sub_const_ball hw.1 (ε n)))
  have hV:H1 B (fun x=>u x+max (w x) 0) V:=
    hu.add (SobolevCalculus.h1_positivePart Metric.isOpen_ball hw.1)
  have hstrong:Tendsto (fun n=>eLpNorm (F n-V) 2 (volume.restrict B)) atTop (𝓝 0) := by
    have hp:∀ᵐ x ∂volume.restrict B,Tendsto (fun n=>w x-ε n) atTop (𝓝 (w x)):=
      Eventually.of_forall fun x=>by simpa only [sub_zero] using tendsto_const_nhds.sub hεlim
    have hWW:Tendsto (fun _n:ℕ=>eLpNorm (W-W) 2 (volume.restrict B)) atTop (𝓝 0):=by
      simp only [sub_self,eLpNorm_zero]
      exact tendsto_const_nhds
    have hh:=SobolevCalculus.positivePart_gradient_strong_of_ae Metric.isOpen_ball
      hw.1 (fun n=>h1_sub_const_ball hw.1 (ε n)) hp hWW
    convert hh using 1
    funext n
    congr 1
    funext x
    dsimp [F,V]
    abel
  have hVe:V =ᵐ[volume.restrict B] (fun x=>G x+W x):=by
    filter_upwards [hwn,SobolevCalculus.gradient_zero_on_zero_set Metric.isOpen_ball hw.1] with x hx h0
    by_cases hp:0<w x
    · simp [V,hp]
    · have hz:w x=0:=le_antisymm (not_lt.mp hp) hx
      simp [V,hp,h0 hz]
  have hnorm:(∫x in B,‖V x‖^2)=(∫x in B,‖G x+W x‖^2):=
    integral_congr_ae (hVe.mono fun x hx=>by
      change ‖V x‖^2=‖G x+W x‖^2
      rw [hx])
  have hlim:=tendsto_integral_norm_sq (fun n=>(hF n).2.1) hV.2.1 hstrong
  rw [hnorm] at hlim
  have hb(n:ℕ):energy B u G≤(∫x in B,‖F n x‖^2)+
      (∫x in B,if 0<u x+w x then (1:ℝ) else 0):=
    fixed_threshold_limit hu hw hun hwn (hε n) (hcomp (ε n) (hε n))
  have hh:=ge_of_tendsto (hlim.add_const (∫x in B,if 0<u x+w x then (1:ℝ) else 0))
    (Eventually.of_forall hb)
  change energy B u G ≤ energy B (fun x=>u x+w x) (fun x=>G x+W x)
  change energy B u G ≤ ∫x in B, ‖G x+W x‖^2 + if 0<u x+w x then (1:ℝ) else 0
  rw [integral_add ((hu.add hw.1).2.1.integrable_norm_pow (by norm_num))
    (integrable_phase (hu.add hw.1).1.aestronglyMeasurable)]
  exact hh
end Bernoulli.ThresholdRecovery

end
end

end OAI
