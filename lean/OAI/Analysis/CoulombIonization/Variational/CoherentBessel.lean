import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.CoherentPhaseBasis

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

namespace CoulombAtom

lemma lp_complex_norm_sq {A : Type*} [MeasurableSpace A] (μ : Measure A) (f : Lp ℂ 2 μ) :
    ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K,← RCLike.ofReal_pow]
  rw [integral_ofReal]
  rfl

lemma coherentPhaseRaw_conjTest {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (i : CoherentIndex hg hcg μ) {F : Space × Space → ℂ} (hF : MemLp F 2 μ) :
    inner ℂ (coherentPhaseRaw hg hcg μ i) (hF.star.toLp (star F)) =
      conj (∫ q, coherentCoefficient hg hcg μ i q * F q ∂μ) := by
  rw [L2.inner_def,← integral_conj]
  apply integral_congr_ae
  filter_upwards [(coherentCoefficient_memLp hg hcg μ i).coeFn_toLp,
    hF.star.coeFn_toLp] with q hi hq
  change inner ℂ ((coherentCoefficient_memLp hg hcg μ i).toLp _ q) _ = _
  rw [hi,hq]
  simp only [RCLike.inner_apply,Pi.star_apply,map_mul,starRingEnd_apply,mul_comm]

lemma coherentPhaseVector_normTest {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (i : CoherentPositiveIndex hg hcg μ) {F : Space × Space → ℂ} (hF : MemLp F 2 μ) :
    ‖inner ℂ (coherentPhaseVector hg hcg μ i) (hF.star.toLp (star F))‖^2 =
      (coherentFactor / coherentWeight hg hcg μ i.1) *
        ‖∫ q, coherentCoefficient hg hcg μ i.1 q * F q ∂μ‖^2 := by
  rw [coherentPhaseVector,inner_smul_left_eq_smul,coherentPhaseRaw_conjTest hg hcg μ i.1 hF,
    norm_smul,Complex.norm_conj,mul_pow,Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (div_nonneg coherentFactor_pos.le i.2.le)]

lemma coherent_synthesis_bessel {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (s : Finset (CoherentPositiveIndex hg hcg μ)) {F : Space × Space → ℂ} (hF : MemLp F 2 μ) :
    (∑ i ∈ s, coherentWeight hg hcg μ i.1 *
      ‖((coherentWeight hg hcg μ i.1)⁻¹ * coherentFactor : ℝ) •
        (∫ q, coherentCoefficient hg hcg μ i.1 q * F q ∂μ)‖^2) ≤
      coherentFactor * ∫ q, ‖F q‖^2 ∂μ := by
  have hb := (coherentPhaseVector_orthonormal hg hcg μ).sum_inner_products_le
    (s := s) (hF.star.toLp (star F))
  have hn : ‖hF.star.toLp (star F)‖^2 = ∫ q, ‖F q‖^2 ∂μ := by
    rw [lp_complex_norm_sq]
    apply integral_congr_ae
    filter_upwards [hF.star.coeFn_toLp] with q hq
    rw [hq]
    simp only [Pi.star_apply,norm_star]
  rw [hn] at hb
  have he (i : CoherentPositiveIndex hg hcg μ) :
      coherentWeight hg hcg μ i.1 *
        ‖((coherentWeight hg hcg μ i.1)⁻¹ * coherentFactor : ℝ) •
          (∫ q, coherentCoefficient hg hcg μ i.1 q * F q ∂μ)‖^2 =
      coherentFactor * ‖inner ℂ (coherentPhaseVector hg hcg μ i) (hF.star.toLp (star F))‖^2 := by
    rw [coherentPhaseVector_normTest hg hcg μ i hF,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    field_simp [i.2.ne']
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hb coherentFactor_pos.le

lemma coherentParam_memLp {F : Space × Space → ℂ} (hF : Continuous F)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) : MemLp F 2 μ := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  apply MemLp.of_bound hF.aestronglyMeasurable C
  filter_upwards [hμ] with q hq
  exact hC q hq

lemma coherentOrbital_density_le {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (s : Finset (CoherentPositiveIndex hg hcg μ)) (x : Space) :
    (∑ i ∈ s, coherentWeight hg hcg μ i.1 * ‖coherentOrbital hg hcg μ i.1 x‖^2) ≤
      coherentFactor * ∫ q, ‖coherentPacket g q.1 q.2 x‖^2 ∂μ := by
  have hc : Continuous (fun q : Space × Space => coherentPacket g q.1 q.2 x) := by
    unfold coherentPacket
    fun_prop
  exact coherent_synthesis_bessel hg hcg μ s (coherentParam_memLp hc μ hK hμ)

end CoulombAtom

end

end OAI
