import OAI.Analysis.BernoulliCone.TraceBound

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison
open Foliation

def shiftU (ε:ℝ) (x:Space 7):ℝ:=U x+ε
def ceilingGraph (ε:ℝ) (v:Space 7→ℝ) (x:Space 7):ℝ:=max (shiftU ε x) (v x)
def comparisonR (ε:ℝ) (v:Space 7→ℝ) (x:Space 7):ℝ:=
  if U x+ε<v x then ‖gradient v x‖^2+‖upperFlux (x,U x+ε)‖^2-
    2*inner ℝ (upperFlux (x,U x+ε)) (gradient U x) else 0

lemma shiftU_lipschitz {K:ℝ≥0} (hK:LipschitzWith K U) (ε:ℝ) :
    LipschitzWith K (shiftU ε):=by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [shiftU,dist_add_right] using hK.dist_le_mul x y
lemma ceilingGraph_lipschitz {K L:ℝ≥0} {v:Space 7→ℝ}
    (hK:LipschitzWith K U) (hL:LipschitzWith L v) (ε:ℝ) :
    LipschitzWith (max K L) (ceilingGraph ε v):=(shiftU_lipschitz hK ε).max hL
lemma ceiling_eq_shift_outside {v:Space 7→ℝ} {ε:ℝ} (hε:0≤ε) {x:Space 7}
    (hx:x∉tsupport (fun y=>v y-U y)) : ceilingGraph ε v x=shiftU ε x := by
  have hv:v x=U x:=sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f:=fun y=>v y-U y) hx)
  exact max_eq_left (by dsimp [shiftU]; rw [hv]; linarith)
lemma ceiling_sub_compact {v:Space 7→ℝ} {ε:ℝ} (hε:0≤ε)
    (hc:HasCompactSupport (fun y=>v y-U y)) :
    HasCompactSupport (fun x=>ceilingGraph ε v x-shiftU ε x) := by
  apply HasCompactSupport.intro hc
  intro x hx
  rw [ceiling_eq_shift_outside hε hx,sub_self]
lemma comparison_primitive_support {v:Space 7→ℝ} {ε:ℝ} (hε:0≤ε) :
    tsupport (verticalPotential upperFlux (shiftU ε) (ceilingGraph ε v))⊆tsupport (fun y=>v y-U y) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have he:=ceiling_eq_shift_outside hε hn
  exact hx (by simp [verticalPotential,he])
lemma comparison_primitive_compact {v:Space 7→ℝ} {ε:ℝ} (hε:0≤ε)
    (hc:HasCompactSupport (fun y=>v y-U y)) :
    HasCompactSupport (verticalPotential upperFlux (shiftU ε) (ceilingGraph ε v)) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (comparison_primitive_support hε)

lemma shiftU_gradient {ε:ℝ} {x:Space 7} (hx:DifferentiableAt ℝ U x) :
    gradient (shiftU ε) x=gradient U x := by
  have hd:HasFDerivAt (shiftU ε) (fderiv ℝ U x) x:=hx.hasFDerivAt.add_const ε
  unfold gradient
  rw [hd.fderiv]
lemma ceilingGraph_gradient {ε:ℝ} {v:Space 7→ℝ} {x:Space 7}
    (hv:ContinuousAt v x) (hlt:U x+ε<v x) :
    gradient (ceilingGraph ε v) x=gradient v x := by
  have he:ceilingGraph ε v =ᶠ[𝓝 x] v:=by
    filter_upwards [(U_continuous.continuousAt.add_const ε).eventually_lt hv hlt] with y hy
    exact max_eq_right hy.le
  unfold gradient
  rw [he.fderiv_eq]

lemma comparisonR_ae_bound {v:Space 7→ℝ} {L:ℝ≥0} (hv:LipschitzWith L v)
    {ε:ℝ} (hε:0<ε) (hc:HasCompactSupport (fun y=>v y-U y)) :
    ∀ᵐ x:Space 7 ∂volume,
      divergence (verticalPotential upperFlux (shiftU ε) (ceilingGraph ε v)) x≤comparisonR ε v x := by
  obtain ⟨K,hK⟩:=exists_lipschitz_U
  have ha:=shiftU_lipschitz hK ε
  have hb:=ceilingGraph_lipschitz hK hv ε
  obtain ⟨M,hM⟩:=clamped_seam_lipschitz ha hb (fun x=>by dsimp [shiftU]; linarith)
    (ceiling_sub_compact hε.le hc)
  filter_upwards [radiusSq_pos_ae,hK.ae_differentiableAt,ha.ae_differentiableAt,
    hb.ae_differentiableAt,hM.ae_differentiableAt] with x hqx hdu hda hdb hdw
  have h:=upperFlux_primitive_bound ha.continuous.continuousAt hb.continuous.continuousAt
    (fun y=>le_max_left _ _) (by dsimp [shiftU]; linarith) hqx hda hdb hdw
  rw [shiftU_gradient hdu] at h
  by_cases hlt:U x+ε<v x
  · have hh:shiftU ε x<ceilingGraph ε v x:=(lt_max_iff.mpr (Or.inr hlt))
    rw [ite_eq_left hh,ceilingGraph_gradient hv.continuous.continuousAt hlt] at h
    simpa only [shiftU,comparisonR,ite_eq_left hlt] using h
  · have hh:¬shiftU ε x<ceilingGraph ε v x:=by
      simpa only [ceilingGraph,shiftU,lt_max_iff,lt_self_iff_false,false_or] using hlt
    simpa only [ite_eq_right hh,comparisonR,ite_eq_right hlt] using h

lemma comparisonR_measurable {v:Space 7→ℝ} (hv:Measurable v) (ε:ℝ):
    Measurable (comparisonR ε v) := by
  have hA:Measurable (fun x:Space 7=>upperFlux (x,U x+ε)):=
    upperFlux_measurable.comp (measurable_id.prodMk (U_continuous.measurable.add_const ε))
  exact ((LipschitzSobolev.measurable_gradient.norm.pow_const 2 |>.add (hA.norm.pow_const 2)).sub
    ((hA.inner LipschitzSobolev.measurable_gradient).const_mul 2)).ite
      (measurableSet_lt (U_continuous.measurable.add_const ε) hv) measurable_const

lemma comparisonR_bound {v:Space 7→ℝ} {K L:ℝ≥0} (hK:LipschitzWith K U)
    (hL:LipschitzWith L v) {C:ℝ} (hC:0≤C) (hA:∀p:Space 7×ℝ,‖upperFlux p‖≤C) (ε:ℝ) (x:Space 7):
    ‖comparisonR ε v x‖≤(L:ℝ)^2+C^2+2*C*K := by
  unfold comparisonR
  split_ifs
  · have h1:‖gradient v x‖^2≤(L:ℝ)^2:=sq_le_sq₀ (norm_nonneg _) L.2 |>.mpr (LipschitzSobolev.norm_gradient_le hL x)
    have h2:‖upperFlux (x,U x+ε)‖^2≤C^2:=sq_le_sq₀ (norm_nonneg _) hC |>.mpr (hA _)
    have h3:‖inner ℝ (upperFlux (x,U x+ε)) (gradient U x)‖≤C*K:=
      (norm_inner_le_norm _ _).trans (mul_le_mul (hA _) (LipschitzSobolev.norm_gradient_le hK x) (norm_nonneg _) hC)
    calc
      _ ≤ ‖(‖gradient v x‖^2+‖upperFlux (x,U x+ε)‖^2)‖+‖2*inner ℝ (upperFlux (x,U x+ε)) (gradient U x)‖:=norm_sub_le _ _
      _ ≤ (L:ℝ)^2+C^2+2*C*K:=by
        rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)),norm_mul]
        norm_num only [Real.norm_ofNat]
        nlinarith
  · simp only [norm_zero]; positivity

/-- The genuine compact graph primitive yields an integrated comparison at
positive height. Hypotheses concern a competitor, never desired minimality. -/
theorem comparisonR_integral_nonneg {v:Space 7→ℝ} {L:ℝ≥0} (hv:LipschitzWith L v)
    {ε:ℝ} (hε:0<ε) (hc:HasCompactSupport (fun y=>v y-U y))
    {c:Space 7} {r:ℝ} (hS:tsupport (fun y=>v y-U y)⊆Metric.ball c r) :
    0≤∫x in Metric.ball c r,comparisonR ε v x := by
  let P:=verticalPotential upperFlux (shiftU ε) (ceilingGraph ε v)
  obtain ⟨K,hK⟩:=exists_lipschitz_U
  have hPc:HasCompactSupport P:=comparison_primitive_compact hε.le hc
  have hPl:LocallyLipschitz P:=upperFlux_primitive_locallyLipschitz
    (shiftU_lipschitz hK ε).locallyLipschitz (ceilingGraph_lipschitz hK hv ε).locallyLipschitz
    (fun x=>le_max_left _ _) (fun x=>by dsimp [shiftU]; linarith)
  obtain ⟨M,hM⟩:=locallyLipschitz_compact_lipschitz hPl hPc
  obtain ⟨C,hC,hA⟩:=upperFlux_uniform_bound
  have hR:IntegrableOn (comparisonR ε v) (Metric.ball c r):=
    (integrableOn_const (μ:=volume) (C:=(L:ℝ)^2+C^2+2*C*K) (measure_ball_lt_top.ne)).mono'
      (comparisonR_measurable hv.continuous.measurable ε).aestronglyMeasurable.restrict
      (Eventually.of_forall (comparisonR_bound hK hv hC.le hA ε))
  have hz:(∫x in Metric.ball c r,divergence P x)=0:=by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=>
      divergence_zero_outside_support (fun hp=>hx (hS (comparison_primitive_support hε.le hp))))]
    exact integral_divergence_compact hM hPc
  rw [←hz]
  exact integral_mono_ae (integrable_divergence_compact hM hPc).integrableOn hR
    ((comparisonR_ae_bound hv hε hc).filter_mono (ae_mono Measure.restrict_le_self))
end Bernoulli.DeSilvaJerison

end
end

end OAI
