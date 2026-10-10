import OAI.Analysis.BernoulliCone.IntegralUpperLimit

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison
open Foliation

def energyDifference (v:Space 7→ℝ) (x:Space 7):ℝ:=
  (‖gradient v x‖^2+if 0<v x then (1:ℝ) else 0)-
  (‖gradient U x‖^2+if 0<U x then (1:ℝ) else 0)

lemma comparisonR_upper_limit {v:Space 7→ℝ} {x:Space 7}
    (hdu:DifferentiableAt ℝ U x) (hdv:DifferentiableAt ℝ v x)
    (hUv:∀y,U y≤v y) (hq:0<Cylindrical.radiusSq axis x)
    {ε:ℕ→ℝ} (hε:∀n,0<ε n) (hεt:Tendsto ε atTop (𝓝 0))
    {η:ℝ} (hη:0<η) : ∀ᶠ n in atTop,comparisonR (ε n) v x<energyDifference v x+η := by
  rcases (hUv x).eq_or_lt with he|hl
  · have hg:=gradient_eq_of_order_contact hdu hdv hUv he
    have hd:energyDifference v x=0:=by simp [energyDifference,←he,←hg]
    filter_upwards [] with n
    have hn:¬U x+ε n<v x:=by rw [←he]; linarith [hε n]
    simpa only [comparisonR,ite_eq_right hn,hd,zero_add] using hη
  · have hvp:0<v x:=(U_nonneg x).trans_lt hl
    have hheight:Tendsto (fun n=>U x+ε n) atTop (𝓝[>] U x):=by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨by simpa using tendsto_const_nhds.add hεt,
        Eventually.of_forall (fun n=>by change U x<U x+ε n; linarith [hε n])⟩
    have hlt:∀ᶠ n in atTop,U x+ε n<v x:=
      (by simpa using tendsto_const_nhds.add hεt : Tendsto (fun n=>U x+ε n) atTop (𝓝 (U x))).eventually (gt_mem_nhds hl)
    rcases (U_nonneg x).eq_or_lt with he0|hp
    · have hu0:U x=0:=he0.symm
      have hg:gradient U x=0:=by
        have hh:=gradient_eq_of_order_contact (differentiableAt_const (c:=(0:ℝ))) hdu U_nonneg he0
        simpa only [gradient_fun_const] using hh.symm
      have hεw:Tendsto ε atTop (𝓝[>] (0:ℝ)):=by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨hεt,Eventually.of_forall hε⟩
      have hn:=hεw.eventually (upperFlux_zero_trace_bound hq hu0 hη)
      filter_upwards [hn,hlt] with n hn hlt
      rw [comparisonR,ite_eq_left hlt]
      simp only [energyDifference,hu0,hg,norm_zero,zero_pow (by norm_num:2≠0),
        ite_eq_left hvp,lt_self_iff_false,ite_false,zero_add,inner_zero_right,mul_zero,sub_zero]
      linarith
    · have hA:Tendsto (fun n=>upperFlux (x,U x+ε n)) atTop (𝓝 (gradient U x)):=
        (upperFlux_tendsto_positive_trace hp).comp hheight
      have ht:Tendsto (fun n=>‖gradient v x‖^2+‖upperFlux (x,U x+ε n)‖^2-
          2*inner ℝ (upperFlux (x,U x+ε n)) (gradient U x)) atTop
          (𝓝 (energyDifference v x)):=by
        have hvc:Tendsto (fun _n:ℕ=>‖gradient v x‖^2) atTop (𝓝 (‖gradient v x‖^2)):=tendsto_const_nhds
        have hgc:Tendsto (fun _n:ℕ=>gradient U x) atTop (𝓝 (gradient U x)):=tendsto_const_nhds
        have hh:=(hvc.add (hA.norm.pow 2)).sub ((hA.inner hgc).const_mul 2)
        convert hh using 1
        simp only [energyDifference,ite_eq_left hp,ite_eq_left hvp,real_inner_self_eq_norm_sq]
        ring_nf
      have hn:=ht.eventually (gt_mem_nhds (by linarith : energyDifference v x<energyDifference v x+η))
      filter_upwards [hn,hlt] with n hn hlt
      simpa only [comparisonR,ite_eq_left hlt] using hn

/-- Actual one-sided global energy comparison for every Lipschitz compact
upper perturbation. All flux/slopes have been constructed explicitly. -/
theorem U_upper_lipschitz_comparison {v:Space 7→ℝ} {L:ℝ≥0}
    (hv:LipschitzWith L v) (hUv:∀x,U x≤v x)
    (hc:HasCompactSupport (fun y=>v y-U y))
    {c:Space 7} {r:ℝ} (hS:tsupport (fun y=>v y-U y)⊆Metric.ball c r) :
    energy (Metric.ball c r) U (gradient U)≤energy (Metric.ball c r) v (gradient v) := by
  let B:=Metric.ball c r
  let μ:=volume.restrict B
  let :IsFiniteMeasure μ:=isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨K,hK⟩:=exists_lipschitz_U
  obtain ⟨C,hC,hA⟩:=upperFlux_uniform_bound
  let ε:ℕ→ℝ:=fun n=>1/((n:ℝ)+1)
  have hε(n:ℕ):0<ε n:=by dsimp [ε]; positivity
  have hεt:Tendsto ε atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  have huH:=LipschitzSobolev.h1_ball hK c r
  have hvH:=LipschitzSobolev.h1_ball hv c r
  have huI:Integrable (fun x=>‖gradient U x‖^2+if 0<U x then (1:ℝ) else 0) μ:=
    (huH.2.1.integrable_norm_pow (by norm_num)).add (integrable_phase huH.1.aestronglyMeasurable)
  have hvI:Integrable (fun x=>‖gradient v x‖^2+if 0<v x then (1:ℝ) else 0) μ:=
    (hvH.2.1.integrable_norm_pow (by norm_num)).add (integrable_phase hvH.1.aestronglyMeasurable)
  have hRi(n:ℕ):Integrable (comparisonR (ε n) v) μ:=
    (integrable_const ((L:ℝ)^2+C^2+2*C*K)).mono'
      (comparisonR_measurable hv.continuous.measurable (ε n)).aestronglyMeasurable
      (Eventually.of_forall (comparisonR_bound hK hv hC.le hA (ε n)))
  have hlim:∀ᵐ x ∂μ,∀η:ℝ,0<η → ∀ᶠ n in atTop,
      comparisonR (ε n) v x<energyDifference v x+η:=by
    have hh:∀ᵐ x:Space 7 ∂volume,∀η:ℝ,0<η → ∀ᶠ n in atTop,
        comparisonR (ε n) v x<energyDifference v x+η:=by
      filter_upwards [hK.ae_differentiableAt,hv.ae_differentiableAt,radiusSq_pos_ae] with x hdu hdv hqx η hη
      exact comparisonR_upper_limit hdu hdv hUv hqx hε hεt hη
    exact hh.filter_mono (ae_mono Measure.restrict_le_self)
  have hi:=integral_nonneg_of_dominated_upper_limit hRi (hvI.sub huI)
    (integrable_const ((L:ℝ)^2+C^2+2*C*K))
    (fun n=>Eventually.of_forall (comparisonR_bound hK hv hC.le hA (ε n)))
    (fun n=>comparisonR_integral_nonneg hv (hε n) hc hS) hlim
  change 0≤∫x,energyDifference v x ∂μ at hi
  rw [show energyDifference v=(fun x=>(‖gradient v x‖^2+if 0<v x then (1:ℝ) else 0)-
    (‖gradient U x‖^2+if 0<U x then (1:ℝ) else 0)) from rfl,integral_sub hvI huI] at hi
  exact sub_nonneg.mp hi
end Bernoulli.DeSilvaJerison

end
end

end OAI
