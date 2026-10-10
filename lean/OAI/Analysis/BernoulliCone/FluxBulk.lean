import OAI.Analysis.BernoulliCone.FoliationBulkGerm

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison
open Foliation
lemma normalized_radius_eq_one_iff {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:0<Cylindrical.radiusSq axis p.1) :
    Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)=1 ↔ seamHeight p.1=p.2 := by
  let l:=upperParameter p.1 p.2
  let r:=Real.sqrt (Cylindrical.radiusSq axis p.1)
  have hl:0<l:=(upperParameter_spec hp).1
  have hr:0<r:=Real.sqrt_pos.mpr hq
  have hr2:r^2=Cylindrical.radiusSq axis p.1:=Real.sq_sqrt hq.le
  have hrl:Cylindrical.radiusSq axis (l⁻¹ • p.1)=1 ↔ l=r:=by
    rw [Cylindrical.radiusSq_smul,inv_pow,←div_eq_inv_mul,div_eq_one_iff_eq (pow_ne_zero 2 hl.ne'),←hr2]
    exact (sq_eq_sq₀ hr.le hl.le).trans eq_comm
  rw [hrl]
  constructor
  · intro he
    have hh:upperFamily r p.1=p.2:=by simpa only [←he] using (upperParameter_spec hp).2
    rw [upperFamily_at_seam hq] at hh
    have ht:0<p.2:=(U_nonneg _).trans_lt hp
    have hs:0<seamHeight p.1:=by
      by_contra hn
      rw [max_eq_right (le_of_not_gt hn)] at hh
      linarith
    rwa [max_eq_left hs.le] at hh
  · intro he
    exact upperParameter_unique hp hr (by rw [upperFamily_at_seam hq,he,max_eq_left ((U_nonneg _).trans hp.le)])

lemma upperFlux_bulk {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    bulkExpression upperFlux p≤0 := by
  rw [bulkExpression_congr (upperFlux_eventually_eq hp hq)]
  exact upperCalibration_bulk hp hq

lemma upperFlux_bulk_off_seam {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:0<Cylindrical.radiusSq axis p.1) (hs:seamHeight p.1≠p.2) :
    bulkExpression upperFlux p≤0 :=
  upperFlux_bulk hp (fun h=>hs ((normalized_radius_eq_one_iff hp hq).mp h))

lemma exteriorFlux_eventually_eq {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:0<Cylindrical.radiusSq axis p.1) (hs:p.2<seamHeight p.1) :
    exteriorFlux =ᶠ[𝓝 p] upperFlux := by
  have hqn:∀ᶠ z:Space 7×ℝ in 𝓝 p,0<Cylindrical.radiusSq axis z.1:=
    ((Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt.comp continuous_fst.continuousAt).eventually (lt_mem_nhds hq)
  have hsn:∀ᶠ z:Space 7×ℝ in 𝓝 p,z.2<seamHeight z.1:=
    continuous_snd.continuousAt.eventually_lt ((seamHeight_contDiffAt hq).continuousAt.comp continuous_fst.continuousAt) hs
  filter_upwards [above_U_isOpen.mem_nhds hp,hqn,hsn] with z hz hzq hzs
  exact (upperFlux_eq_exterior hz hzq hzs).symm
end Bernoulli.DeSilvaJerison

end
end

end OAI
