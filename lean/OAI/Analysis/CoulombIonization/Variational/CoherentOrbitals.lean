import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.CompactEigenbasis
import OAI.Analysis.CoulombIonization.Variational.SmoothCompactIntegral

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

namespace CoulombAtom

lemma coherentOperator_synthesis {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (u : OrbitalHilbert) : coherentOperator hg hcg μ u =
      (((2*Real.pi)^3)⁻¹ : ℝ) • ∫ q, inner ℂ (coherentVector hg hcg q) u •
        coherentVector hg hcg q ∂μ := by
  change (((2*Real.pi)^3)⁻¹ : ℝ) • ((∫ q, InnerProductSpace.rankOne ℂ
    (coherentVector hg hcg q) (coherentVector hg hcg q) ∂μ) u) = _
  rw [ContinuousLinearMap.integral_apply (coherentRankOne_integrable hg hcg μ)]
  simp only [InnerProductSpace.rankOne_apply]

def coherentOrbital {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) : Space → ℂ :=
  ((coherentWeight hg hcg μ i)⁻¹ * ((2*Real.pi)^3)⁻¹ : ℝ) •
    packetSynthesis g μ (fun q => inner ℂ (coherentVector hg hcg q) (coherentBasis hg hcg μ i))

lemma coherentOrbital_smooth {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg.continuous hcg μ) : ContDiff ℝ ∞ (coherentOrbital hg.continuous hcg μ i) := by
  unfold coherentOrbital
  exact (packetSynthesis_smooth hg μ hK hμ
    ((coherentVector_continuous hg.continuous hcg).inner continuous_const)).const_smul
      ((coherentWeight hg.continuous hcg μ i)⁻¹ * ((2*Real.pi)^3)⁻¹ : ℝ)

lemma coherentOrbital_zero_outside {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg hcg μ) {x : Space} (hx : x ∉ coherentSpatialSupport g K) :
    coherentOrbital hg hcg μ i x = 0 := by
  simp only [coherentOrbital,Pi.smul_apply,packetSynthesis_zero_outside μ hμ _ hx,smul_zero]

lemma coherentOrbital_compact {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg hcg μ) : HasCompactSupport (coherentOrbital hg hcg μ i) :=
  (packetSynthesis_compact hcg μ hK hμ _).smul_left

lemma coherentOrbital_memLp {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg.continuous hcg μ) : MemLp (coherentOrbital hg.continuous hcg μ i) 2 :=
  (packetSynthesis_memLp hg hcg μ hK hμ
    ((coherentVector_continuous hg.continuous hcg).inner continuous_const)).const_smul _

lemma coherentOrbital_toLp {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg.continuous hcg μ) (hi : coherentWeight hg.continuous hcg μ i ≠ 0) :
    (coherentOrbital_memLp hg hcg μ hK hμ i).toLp (coherentOrbital hg.continuous hcg μ i) =
      coherentBasis hg.continuous hcg μ i := by
  have hw : Continuous (fun q => inner ℂ (coherentVector hg.continuous hcg q)
      (coherentBasis hg.continuous hcg μ i)) :=
    (coherentVector_continuous hg.continuous hcg).inner continuous_const
  have hm := packetSynthesis_memLp hg hcg μ hK hμ hw
  change (hm.const_smul ((coherentWeight hg.continuous hcg μ i)⁻¹ *
    ((2*Real.pi)^3)⁻¹ : ℝ)).toLp _ = _
  rw [MemLp.toLp_const_smul _ hm,packetSynthesis_toLp hg hcg μ hK hμ hw,
    mul_smul,← coherentOperator_synthesis,coherentBasis_real_eigen,smul_smul,
    inv_mul_cancel₀ hi,one_smul]

lemma coherentOrbital_ae {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg.continuous hcg μ) (hi : coherentWeight hg.continuous hcg μ i ≠ 0) :
    coherentBasis hg.continuous hcg μ i =ᵐ[volume] coherentOrbital hg.continuous hcg μ i := by
  rw [← coherentOrbital_toLp hg hcg μ hK hμ i hi]
  exact MemLp.coeFn_toLp _

lemma coherentOrbital_inner {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i j : CoherentIndex hg.continuous hcg μ)
    (hi : coherentWeight hg.continuous hcg μ i ≠ 0)
    (hj : coherentWeight hg.continuous hcg μ j ≠ 0) :
    (∫ x : Space, conj (coherentOrbital hg.continuous hcg μ i x) *
      coherentOrbital hg.continuous hcg μ j x) =
      inner ℂ (coherentBasis hg.continuous hcg μ i) (coherentBasis hg.continuous hcg μ j) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coherentOrbital_ae hg hcg μ hK hμ i hi,
    coherentOrbital_ae hg hcg μ hK hμ j hj] with x hi hj
  rw [hi,hj]
  simp only [RCLike.inner_apply,mul_comm]

end CoulombAtom

end

end OAI
