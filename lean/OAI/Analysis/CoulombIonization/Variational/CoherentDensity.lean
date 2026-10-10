import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.CoherentPhaseBasis

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

namespace CoulombAtom

def coherentDensity (g : Space → ℂ) (μ : Measure (Space × Space)) (x : Space) : ℝ :=
  coherentFactor * ∫ q, ‖coherentPacket g q.1 q.2 x‖^2 ∂μ

lemma coherentDensity_nonneg (g : Space → ℂ) (μ : Measure (Space × Space)) (x : Space) :
    0 ≤ coherentDensity g μ x :=
  mul_nonneg coherentFactor_pos.le (integral_nonneg (fun _ => sq_nonneg _))

lemma coherentDensity_continuous {g : Space → ℂ} (hg : Continuous g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) :
    Continuous (coherentDensity g μ) := by
  have hc : Continuous (fun r : Space × (Space × Space) =>
      ‖coherentPacket g r.2.1 r.2.2 r.1‖^2) := by
    unfold coherentPacket
    fun_prop
  have h := continuous_parametric_integral_of_continuous (μ := μ)
    (f := fun (x : Space) (q : Space × Space) => ‖coherentPacket g q.1 q.2 x‖^2) hc hK
  rw [Measure.restrict_eq_self_of_ae_mem hμ] at h
  exact continuous_const.mul h

lemma coherentDensity_zero_outside {g : Space → ℂ}
    (μ : Measure (Space × Space)) {K : Set (Space × Space)} (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {x : Space} (hx : x ∉ coherentSpatialSupport g K) : coherentDensity g μ x = 0 := by
  have he : (∫ q, ‖coherentPacket g q.1 q.2 x‖^2 ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hμ] with q hq
    simp only [coherentPacket_zero_outside hq hx,norm_zero,zero_pow (by decide : 2 ≠ 0),Pi.zero_apply]
  simp only [coherentDensity,he,mul_zero]

lemma coherentDensity_compact {g : Space → ℂ} (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) {K : Set (Space × Space)} (hK : IsCompact K)
    (hμ : ∀ᵐ q ∂μ, q ∈ K) : HasCompactSupport (coherentDensity g μ) := by
  apply HasCompactSupport.of_support_subset_isCompact (coherentSpatialSupport_compact hcg hK)
  intro x hx
  by_contra hn
  exact hx (coherentDensity_zero_outside μ hμ hn)

lemma coherentDensity_integrable {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) :
    Integrable (coherentDensity g μ) :=
  (coherentDensity_continuous hg μ hK hμ).integrable_of_hasCompactSupport
    (coherentDensity_compact hcg μ hK hμ)

lemma coherentPacket_sq_integrable {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) :
    Integrable (fun r : (Space × Space) × Space =>
      ‖coherentPacket g r.1.1 r.1.2 r.2‖^2) (μ.prod volume) := by
  have hc : Continuous (fun r : (Space × Space) × Space =>
      ‖coherentPacket g r.1.1 r.1.2 r.2‖^2) := by
    unfold coherentPacket
    fun_prop
  have hi := hc.continuousOn.integrableOn_compact
    (hK.prod (coherentSpatialSupport_compact hcg hK)) (μ := μ.prod volume)
  apply hi.integrable_of_ae_notMem_eq_zero
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμ] with r hr
  intro hn
  have hx : r.2 ∉ coherentSpatialSupport g K := fun hx => hn ⟨hr,hx⟩
  simp only [coherentPacket_zero_outside hr hx,norm_zero,zero_pow (by decide : 2 ≠ 0)]

lemma coherentPacket_mass {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (q : Space × Space) : (∫ x : Space, ‖coherentPacket g q.1 q.2 x‖^2) = ∫ x : Space, ‖g x‖^2 := by
  rw [← coherentVector_norm_sq hg hcg q,lp_norm_sq]
  apply integral_congr_ae
  filter_upwards [coherentVector_coe hg hcg q] with x hx
  rw [hx]

lemma coherentDensity_mass {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) :
    (∫ x : Space, coherentDensity g μ x) =
      coherentFactor * μ.real Set.univ * ∫ x : Space, ‖g x‖^2 := by
  have hi : Integrable (fun r : Space × (Space × Space) =>
      ‖coherentPacket g r.2.1 r.2.2 r.1‖^2) (volume.prod μ) :=
    (coherentPacket_sq_integrable hg hcg μ hK hμ).swap
  simp only [coherentDensity,integral_const_mul]
  rw [integral_integral_swap (f := fun (x : Space) (q : Space × Space) =>
    ‖coherentPacket g q.1 q.2 x‖^2) hi]
  simp only [coherentPacket_mass hg hcg,integral_const,smul_eq_mul,mul_assoc]

lemma coherentPositiveWeight_hasSum {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    HasSum (fun i : CoherentPositiveIndex hg hcg μ => coherentWeight hg hcg μ i.1)
      (coherentFactor * μ.real Set.univ * ∫ x : Space, ‖g x‖^2) := by
  apply (hasSum_subtype_iff_of_support_subset (f := coherentWeight hg hcg μ) ?_).2
    (coherentWeight_hasSum hg hcg μ)
  intro i hi
  exact lt_of_le_of_ne (coherentWeight_nonneg hg hcg μ i) (Ne.symm hi)

lemma coherentOrbital_mass {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentPositiveIndex hg.continuous hcg μ) :
    (∫ x : Space, ‖coherentOrbital hg.continuous hcg μ i.1 x‖^2) = 1 := by
  have he : (∫ x : Space, ‖coherentOrbital hg.continuous hcg μ i.1 x‖^2) =
      ‖coherentBasis hg.continuous hcg μ i.1‖^2 := by
    rw [lp_norm_sq]
    exact integral_congr_ae ((coherentOrbital_ae hg hcg μ hK hμ i.1 i.2.ne').symm.fun_comp
      (fun z : ℂ => ‖z‖^2))
  rw [he,(coherentBasis hg.continuous hcg μ).orthonormal.norm_eq_one,one_pow]

end CoulombAtom

end

end OAI
