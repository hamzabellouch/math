import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoherentOrbitals

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

namespace CoulombAtom

def coherentFactor : ℝ := ((2*Real.pi)^3)⁻¹
lemma coherentFactor_pos : 0 < coherentFactor := by unfold coherentFactor; positivity

lemma coherentVector_norm_eq {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (q r : Space × Space) :
    ‖coherentVector hg hcg q‖ = ‖coherentVector hg hcg r‖ := by
  have hq := coherentVector_norm_sq hg hcg q
  have hr := coherentVector_norm_sq hg hcg r
  nlinarith [norm_nonneg (coherentVector hg hcg q),norm_nonneg (coherentVector hg hcg r)]

lemma coherentOperator_mixed {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (u v : OrbitalHilbert) : inner ℂ u (coherentOperator hg hcg μ v) =
      coherentFactor • ∫ q, conj (inner ℂ (coherentVector hg hcg q) u) *
        inner ℂ (coherentVector hg hcg q) v ∂μ := by
  have hi : Integrable (fun q => inner ℂ (coherentVector hg hcg q) v •
      coherentVector hg hcg q) μ := by
    have h := (ContinuousLinearMap.apply ℂ OrbitalHilbert v).integrable_comp
      (coherentRankOne_integrable hg hcg μ)
    change Integrable (fun q => InnerProductSpace.rankOne ℂ (coherentVector hg hcg q)
      (coherentVector hg hcg q) v) μ at h
    simpa only [InnerProductSpace.rankOne_apply] using h
  rw [coherentOperator_synthesis,inner_smul_right_eq_smul,← integral_inner (𝕜 := ℂ) hi u]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with q
  rw [inner_smul_right,inner_conj_symm]
  ring

def coherentCoefficient {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (i : CoherentIndex hg hcg μ) (q : Space × Space) : ℂ :=
  inner ℂ (coherentVector hg hcg q) (coherentBasis hg hcg μ i)

lemma coherentCoefficient_memLp {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) :
    MemLp (coherentCoefficient hg hcg μ i) 2 μ := by
  apply MemLp.of_bound (((coherentVector_continuous hg hcg).inner
    continuous_const).aestronglyMeasurable) ‖coherentVector hg hcg (0,0)‖
  filter_upwards [] with q
  calc
    _ ≤ ‖coherentVector hg hcg q‖ * ‖coherentBasis hg hcg μ i‖ := norm_inner_le_norm _ _
    _ = _ := by rw [(coherentBasis hg hcg μ).orthonormal.norm_eq_one,mul_one,coherentVector_norm_eq hg hcg q (0,0)]

def coherentPhaseRaw {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) : Lp ℂ 2 μ :=
  (coherentCoefficient_memLp hg hcg μ i).toLp _

lemma coherentPhaseRaw_inner {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (i j : CoherentIndex hg hcg μ) :
    coherentFactor • inner ℂ (coherentPhaseRaw hg hcg μ i) (coherentPhaseRaw hg hcg μ j) =
      coherentWeight hg hcg μ j • inner ℂ (coherentBasis hg hcg μ i) (coherentBasis hg hcg μ j) := by
  have he : inner ℂ (coherentPhaseRaw hg hcg μ i) (coherentPhaseRaw hg hcg μ j) =
      ∫ q, conj (coherentCoefficient hg hcg μ i q) * coherentCoefficient hg hcg μ j q ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(coherentCoefficient_memLp hg hcg μ i).coeFn_toLp,
      (coherentCoefficient_memLp hg hcg μ j).coeFn_toLp] with q hi hj
    simp only [coherentPhaseRaw] at ⊢
    rw [hi,hj]
    simp only [RCLike.inner_apply,mul_comm]
  rw [he]
  change coherentFactor • (∫ q, conj (inner ℂ (coherentVector hg hcg q) _) *
    inner ℂ (coherentVector hg hcg q) _ ∂μ) = _
  rw [← coherentOperator_mixed,coherentBasis_real_eigen,inner_smul_right_eq_smul]

abbrev CoherentPositiveIndex {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) := {i : CoherentIndex hg hcg μ // 0 < coherentWeight hg hcg μ i}

def coherentPhaseVector {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentPositiveIndex hg hcg μ) : Lp ℂ 2 μ :=
  Real.sqrt (coherentFactor / coherentWeight hg hcg μ i.1) • coherentPhaseRaw hg hcg μ i.1

lemma coherentPhaseVector_orthonormal {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    Orthonormal ℂ (coherentPhaseVector hg hcg μ) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  have hraw : inner ℂ (coherentPhaseRaw hg hcg μ i.1) (coherentPhaseRaw hg hcg μ j.1) =
      (coherentWeight hg hcg μ j.1 / coherentFactor) •
        inner ℂ (coherentBasis hg hcg μ i.1) (coherentBasis hg hcg μ j.1) := by
    have h := congrArg (fun z : ℂ => coherentFactor⁻¹ • z) (coherentPhaseRaw_inner hg hcg μ i.1 j.1)
    simpa only [smul_smul,inv_mul_cancel₀ coherentFactor_pos.ne',one_smul,div_eq_mul_inv,mul_comm] using h
  rw [coherentPhaseVector,coherentPhaseVector,inner_smul_left_eq_smul,inner_smul_right_eq_smul,hraw]
  by_cases hij : i=j
  · subst j
    rw [(orthonormal_iff_ite.mp (coherentBasis hg hcg μ).orthonormal),ite_eq_left rfl,ite_eq_left rfl]
    rw [smul_smul,smul_smul]
    have he : Real.sqrt (coherentFactor / coherentWeight hg hcg μ i.1) *
        Real.sqrt (coherentFactor / coherentWeight hg hcg μ i.1) *
          (coherentWeight hg hcg μ i.1 / coherentFactor) = 1 := by
      rw [← pow_two,Real.sq_sqrt (div_nonneg coherentFactor_pos.le i.2.le)]
      field_simp [coherentFactor_pos.ne',i.2.ne']
    rw [he,one_smul]
  · have hval : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    rw [(orthonormal_iff_ite.mp (coherentBasis hg hcg μ).orthonormal),ite_eq_right hval,ite_eq_right hij]
    simp

end CoulombAtom

end

end OAI
