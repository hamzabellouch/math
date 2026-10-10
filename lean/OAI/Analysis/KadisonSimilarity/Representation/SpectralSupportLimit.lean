import OAI.Analysis.KadisonSimilarity.Representation.RegularizedPolarFactor
import OAI.Analysis.KadisonSimilarity.Representation.SpectralStepDischarge
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace OAI

/-! Positive resolvent approximations to the concrete range-support
projection. This gives the strong limit needed for the dihedral arc's
spectral moments, with operator norm bounded by one throughout. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def supportResolvent (B : H →L[ℂ] H) (ε : ℝ) : H →L[ℂ] H :=
  B * positiveShiftReciprocal B ε

theorem supportResolvent_norm_le (B : H →L[ℂ] H) (hB : 0 ≤ B)
    {ε : ℝ} (hε : 0 < ε) : ‖supportResolvent B ε‖ ≤ 1 :=
  positiveShiftReciprocal_mul_norm_le B hB hε

theorem supportResolvent_selfAdjoint (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (ε : ℝ) : IsSelfAdjoint (supportResolvent B ε) := by
  apply (hB.commute_iff (positiveShiftReciprocal_selfAdjoint B ε)).mp
  exact (positiveShiftReciprocal_commute B ε).symm

theorem supportResolvent_mul_support (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (ε : ℝ) : supportResolvent B ε * rangeSupport B = supportResolvent B ε := by
  have h : rangeSupport B * supportResolvent B ε = supportResolvent B ε := by
    rw [supportResolvent, ← mul_assoc, rangeSupport_mul]
  have hs := congrArg star h
  simpa only [star_mul, (rangeSupport_isStarProjection B).isSelfAdjoint.star_eq,
    (supportResolvent_selfAdjoint B hB ε).star_eq] using hs

theorem supportResolvent_range_error (B : H →L[ℂ] H) (hB : 0 ≤ B)
    {ε : ℝ} (hε : 0 < ε) (y : H) :
    ‖supportResolvent B ε (B y) - B y‖ ≤ ε * ‖y‖ := by
  have he := regularizedPolar_error B B hB
    (by rw [hB.isSelfAdjoint.star_eq]) hε
  have he' : ‖supportResolvent B ε * B - B‖ ≤ ε := by
    rw [norm_sub_rev]
    simpa only [supportResolvent, mul_assoc] using he
  calc
    _ = ‖(supportResolvent B ε * B - B) y‖ := rfl
    _ ≤ ‖supportResolvent B ε * B - B‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε * ‖y‖ := mul_le_mul_of_nonneg_right he' (norm_nonneg _)

/-- The positive resolvents converge strongly to the actual range projection. -/
theorem supportResolvent_tendsto (B : H →L[ℂ] H) (hB : 0 ≤ B)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => supportResolvent B (ε n) x) atTop (𝓝 (rangeSupport B x)) := by
  have hequi : Equicontinuous (fun n x => supportResolvent B (ε n) x) :=
    (LipschitzWith.uniformEquicontinuous _ 1 (fun n =>
      ContinuousLinearMap.lipschitzWith_of_opNorm_le (supportResolvent_norm_le B hB (hε n)))).equicontinuous
  have hclosed : IsClosed {y : H |
      Tendsto (fun n => supportResolvent B (ε n) y) atTop (𝓝 y)} :=
    hequi.isClosed_setOfPred_tendsto continuous_id
  have hrange : (B.range : Set H) ⊆ {y : H |
      Tendsto (fun n => supportResolvent B (ε n) y) atTop (𝓝 y)} := by
    rintro _ ⟨y, rfl⟩
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => supportResolvent_range_error B hB (hε n) y)
    simpa only [zero_mul] using hlim.mul_const ‖y‖
  have hx := (closure_minimal hrange hclosed)
    ((operatorRangeClosure B).starProjection_apply_mem x)
  change Tendsto (fun n => supportResolvent B (ε n) (rangeSupport B x)) atTop
    (𝓝 (rangeSupport B x)) at hx
  have heq (n : ℕ) : supportResolvent B (ε n) (rangeSupport B x) =
      supportResolvent B (ε n) x :=
    congrArg (fun T : H →L[ℂ] H => T x) (supportResolvent_mul_support B hB.isSelfAdjoint (ε n))
  simpa only [heq] using hx

end KadisonSimilarity

end

end OAI
