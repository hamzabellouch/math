import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoherentBessel

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

namespace CoulombAtom

lemma coherentPacket_derivative_joint_continuous {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (v : Space) :
    Continuous (fun r : Space × (Space × Space) =>
      fderiv ℝ (coherentPacket g r.2.1 r.2.2) r.1 v) := by
  have hF := coherentPacket_joint_smooth hg
  have he : (fun r : Space × (Space × Space) =>
      fderiv ℝ (coherentPacket g r.2.1 r.2.2) r.1 v) =
      (fun r => firstPartial (fun t : Space × (Space × Space) =>
        coherentPacket g t.2.1 t.2.2 t.1) r v) := by
    funext r
    rw [(firstPartial_hasFDerivAt (hF.differentiable (by simp)) r.1 r.2).fderiv]
  rw [he]
  exact (firstPartial_contDiff (n := 0) (hF.of_le (by norm_num))).continuous.clm_apply continuous_const

lemma packetSynthesis_fderiv_apply {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {w : Space × Space → ℂ} (hw : Continuous w) (x v : Space) :
    fderiv ℝ (packetSynthesis g μ w) x v =
      ∫ q, w q * fderiv ℝ (coherentPacket g q.1 q.2) x v ∂μ := by
  let F : Space × (Space × Space) → ℂ := fun t => coherentPacket g t.2.1 t.2.2 t.1
  have hF : ContDiff ℝ ∞ F := coherentPacket_joint_smooth hg
  have hd := weightedSetIntegral_hasFDerivAt μ K hK (hF.of_le (by norm_num)) hw x
  rw [Measure.restrict_eq_self_of_ae_mem hμ] at hd
  have hi : Integrable (fun q => w q • firstPartial F (x,q)) μ := by
    rw [← Measure.restrict_eq_self_of_ae_mem hμ]
    exact (hw.smul ((firstPartial_contDiff (n := 0) (hF.of_le (by norm_num))).continuous.comp
      (continuous_const.prodMk continuous_id))).continuousOn.integrableOn_compact hK
  change fderiv ℝ (fun y => ∫ q, w q • F (y,q) ∂μ) x v = _
  rw [hd.fderiv,ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [smul_apply]
  have he := (firstPartial_hasFDerivAt (hF.differentiable (by simp)) x q).fderiv
  exact congrArg (fun A : Space →L[ℝ] ℂ => w q • A v) he.symm

lemma coherentOrbital_fderiv_apply {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg.continuous hcg μ) (x v : Space) :
    fderiv ℝ (coherentOrbital hg.continuous hcg μ i) x v =
      ((coherentWeight hg.continuous hcg μ i)⁻¹ * coherentFactor : ℝ) •
        (∫ q, coherentCoefficient hg.continuous hcg μ i q *
          fderiv ℝ (coherentPacket g q.1 q.2) x v ∂μ) := by
  have hw : Continuous (coherentCoefficient hg.continuous hcg μ i) :=
    (coherentVector_continuous hg.continuous hcg).inner continuous_const
  have hd := (packetSynthesis_smooth hg μ hK hμ hw).differentiable (by simp)
  change fderiv ℝ (((coherentWeight hg.continuous hcg μ i)⁻¹ * coherentFactor : ℝ) •
    packetSynthesis g μ (coherentCoefficient hg.continuous hcg μ i)) x v = _
  rw [fderiv_const_smul (hd x),smul_apply,
    packetSynthesis_fderiv_apply hg μ hK hμ hw]

lemma coherentOrbital_gradient_le {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (s : Finset (CoherentPositiveIndex hg.continuous hcg μ)) (x v : Space) :
    (∑ i ∈ s, coherentWeight hg.continuous hcg μ i.1 *
      ‖fderiv ℝ (coherentOrbital hg.continuous hcg μ i.1) x v‖^2) ≤
      coherentFactor * ∫ q, ‖fderiv ℝ (coherentPacket g q.1 q.2) x v‖^2 ∂μ := by
  simp_rw [coherentOrbital_fderiv_apply hg hcg μ hK hμ]
  apply coherent_synthesis_bessel hg.continuous hcg μ s
  apply coherentParam_memLp _ μ hK hμ
  exact (coherentPacket_derivative_joint_continuous hg v).comp
    (continuous_const.prodMk continuous_id)

end CoulombAtom

end

end OAI
