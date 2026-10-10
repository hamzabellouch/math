import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.CoherentDerivatives

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ContDiff Topology

namespace CoulombAtom

lemma coherentPacket_tsupport_subset {g : Space → ℂ} (hcg : HasCompactSupport g)
    {K : Set (Space × Space)} (hK : IsCompact K) {q : Space × Space} (hq : q ∈ K) :
    tsupport (coherentPacket g q.1 q.2) ⊆ coherentSpatialSupport g K := by
  apply closure_minimal _ (coherentSpatialSupport_compact hcg hK).isClosed
  intro x hx
  by_contra hn
  exact hx (coherentPacket_zero_outside hq hn)

lemma coherentPacket_derivative_zero_outside {g : Space → ℂ} (hcg : HasCompactSupport g)
    {K : Set (Space × Space)} (hK : IsCompact K) {q : Space × Space} (hq : q ∈ K)
    {x : Space} (hx : x ∉ coherentSpatialSupport g K) (v : Space) :
    fderiv ℝ (coherentPacket g q.1 q.2) x v = 0 := by
  rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (coherentPacket_tsupport_subset hcg hK hq h))]
  rfl

lemma coherentPacket_derivative_sq_integrable {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) (v : Space) :
    Integrable (fun r : (Space × Space) × Space =>
      ‖fderiv ℝ (coherentPacket g r.1.1 r.1.2) r.2 v‖^2) (μ.prod volume) := by
  have hc : Continuous (fun r : (Space × Space) × Space =>
      ‖fderiv ℝ (coherentPacket g r.1.1 r.1.2) r.2 v‖^2) :=
    ((coherentPacket_derivative_joint_continuous hg v).comp continuous_swap).norm.pow 2
  have hi := hc.continuousOn.integrableOn_compact
    (hK.prod (coherentSpatialSupport_compact hcg hK)) (μ := μ.prod volume)
  apply hi.integrable_of_ae_notMem_eq_zero
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμ] with r hr
  intro hn
  have hx : r.2 ∉ coherentSpatialSupport g K := fun hx => hn ⟨hr,hx⟩
  simp only [coherentPacket_derivative_zero_outside hcg hK hr hx v,
    norm_zero,zero_pow (by decide : 2 ≠ 0)]

lemma coherentOrbital_derivative_sq_integrable {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg.continuous hcg μ) (v : Space) :
    Integrable (fun x : Space => ‖fderiv ℝ (coherentOrbital hg.continuous hcg μ i) x v‖^2) := by
  have hc := (coherentOrbital_compact hg.continuous hcg μ hK hμ i).fderiv_apply ℝ v
  have hd : Continuous (fun x : Space => fderiv ℝ (coherentOrbital hg.continuous hcg μ i) x v) :=
    ((coherentOrbital_smooth hg hcg μ hK hμ i).continuous_fderiv (by simp)).clm_apply continuous_const
  exact (hd.memLp_of_hasCompactSupport hc (p := 2)).norm.integrable_sq

lemma coherentOrbital_kinetic_le {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (s : Finset (CoherentPositiveIndex hg.continuous hcg μ)) (v : Space) :
    (∑ i ∈ s, coherentWeight hg.continuous hcg μ i.1 * ∫ x : Space,
      ‖fderiv ℝ (coherentOrbital hg.continuous hcg μ i.1) x v‖^2) ≤
      coherentFactor * ∫ q, (∫ x : Space, ‖fderiv ℝ (coherentPacket g q.1 q.2) x v‖^2) ∂μ := by
  have hi : Integrable (fun r : Space × (Space × Space) =>
      ‖fderiv ℝ (coherentPacket g r.2.1 r.2.2) r.1 v‖^2) (volume.prod μ) :=
    (coherentPacket_derivative_sq_integrable hg hcg μ hK hμ v).swap
  calc
    _ = ∫ x : Space, ∑ i ∈ s, coherentWeight hg.continuous hcg μ i.1 *
        ‖fderiv ℝ (coherentOrbital hg.continuous hcg μ i.1) x v‖^2 := by
      rw [integral_finsetSum _ (fun i _ =>
        (coherentOrbital_derivative_sq_integrable hg hcg μ hK hμ i.1 v).const_mul _)]
      simp only [integral_const_mul]
    _ ≤ ∫ x : Space, coherentFactor * ∫ q,
        ‖fderiv ℝ (coherentPacket g q.1 q.2) x v‖^2 ∂μ := by
      apply integral_mono
      · exact integrable_finsetSum _ (fun i _ =>
          (coherentOrbital_derivative_sq_integrable hg hcg μ hK hμ i.1 v).const_mul _)
      · exact hi.integral_prod_left.const_mul _
      · exact fun x => coherentOrbital_gradient_le hg hcg μ hK hμ s x v
    _ = _ := by
      rw [integral_const_mul,integral_integral_swap hi]

end CoulombAtom

end

end OAI
