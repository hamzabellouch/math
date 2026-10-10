import OAI.Analysis.BernoulliCone.SmoothLocalizedExtension

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

def exteriorFlux (p:Space 7×ℝ):Space 7:=κ • gradient Zsigned p.1+
  ((p.2-κ*Zsigned p.1)/KSup p.1) • gradient KSup p.1
lemma exteriorFlux_contDiffAt {p:Space 7×ℝ} (hq:0<Cylindrical.radiusSq axis p.1) :
    ContDiffAt ℝ ∞ exteriorFlux p := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hZ:ContDiffAt ℝ ∞ Zsigned p.1:=signed_contDiffAt hx ha
  have hK:ContDiffAt ℝ ∞ KSup p.1:=KSup_contDiffAt hx ha
  have hgZ:ContDiffAt ℝ ∞ (gradient Zsigned) p.1:=
    (toDual ℝ (Space 7)).symm.contDiff.contDiffAt.comp p.1 (hZ.fderiv_right (by simp))
  have hgK:ContDiffAt ℝ ∞ (gradient KSup) p.1:=
    (toDual ℝ (Space 7)).symm.contDiff.contDiffAt.comp p.1 (hK.fderiv_right (by simp))
  exact ((hgZ.comp p contDiffAt_fst).const_smul κ).add
    (((contDiffAt_snd.sub (contDiffAt_const.mul (hZ.comp p contDiffAt_fst))).div
      (hK.comp p contDiffAt_fst) (KSup_pos hx ha).ne').smul (hgK.comp p contDiffAt_fst))
lemma upperFlux_eq_exterior {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:0<Cylindrical.radiusSq axis p.1) (ht:p.2<seamHeight p.1) :
    upperFlux p=exteriorFlux p := by
  have hqn:¬Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≤1:=
    fun h=>not_lt.mpr ((upperParameter_seam_iff hp hq).mp h) ht
  have hqs:(upperParameter p.1 p.2)^2<Cylindrical.radiusSq axis p.1:=by
    have hl:0<upperParameter p.1 p.2:=(upperParameter_spec hp).1
    have hh:1<Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1):=not_le.mp hqn
    rw [Cylindrical.radiusSq_smul,inv_pow,←div_eq_inv_mul,lt_div_iff₀ (sq_pos_of_pos hl),one_mul] at hh
    exact hh
  rw [upperFlux_eq_calibration hp (ne_of_gt (not_le.mp hqn)),upperCalibration_outer_affine hp hqs]
  rfl

/-- The actual two branch fields have global C1 representatives on any compact
positive-height tube away from the axis. Only the cap-side field is extended
from a one-sided region; the full discontinuous flux is never declared smooth. -/
theorem compact_branch_extensions {K:Set (Space 7×ℝ)} (hK:IsCompact K)
    (hp:∀p∈K,U p.1<p.2) (hq:∀p∈K,0<Cylindrical.radiusSq axis p.1) :
    ∃A B:Space 7×ℝ→Space 7,ContDiff ℝ 1 A ∧ ContDiff ℝ 1 B ∧
      EqOn A exteriorFlux K ∧
      ∀p∈K,seamHeight p.1≤p.2 → B p=upperFlux p := by
  let D:Set (Space 7×ℝ):={p|0<Cylindrical.radiusSq axis p.1}
  have hD:IsOpen D:=isOpen_lt continuous_const
    ((Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.comp continuous_fst)
  have hKD:K⊆D:=hq
  obtain ⟨A,hA,hAe⟩:=LocalExtension.exists_contDiff_extension (n:=1) hK hD hKD
    (fun p hpd=>(exteriorFlux_contDiffAt hpd).of_le (by simp) |>.contDiffWithinAt)
  let S:Set (Space 7×ℝ):={p∈K|seamHeight p.1≤p.2}
  have hσ:ContinuousOn (fun p:Space 7×ℝ=>seamHeight p.1) K:=by
    intro p hpk
    exact ((seamHeight_contDiffAt (hq p hpk)).continuousAt.comp continuous_fst.continuousAt).continuousWithinAt
  have hS:IsClosed S:=hK.isClosed.isClosed_le hσ continuousOn_snd
  obtain ⟨B,hB,hBe⟩:=LocalExtension.exists_contDiff_one_of_closed_germs hS (F:=upperFlux) (by
    intro p hps
    have hqp:=((upperParameter_seam_iff (hp p hps.1) (hq p hps.1)).mpr hps.2)
    obtain ⟨C,hC,hCp,hCe⟩:=upperFlux_cap_local_extension (hp p hps.1) hqp
    refine ⟨C,hC.of_le (by simp),?_⟩
    filter_upwards [hCe] with y hy hys
    exact hy (hp y hys.1) ((upperParameter_seam_iff (hp y hys.1) (hq y hys.1)).mpr hys.2))
  refine ⟨A,B,hA,hB,?_,?_⟩
  · intro p hpk
    exact (hAe.filter_mono (nhds_le_nhdsSet hpk)).self_of_nhds
  · intro p hpk hpt
    exact hBe ⟨hpk,hpt⟩
end Bernoulli.DeSilvaJerison

end
end

end OAI
