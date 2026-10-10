import Mathlib.Analysis.Normed.Lp.SmoothApprox
import OAI.Geometry.NodalSets.Elliptic.RealDifferenceQuotientTest

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_L2_norm_le_of_smooth_test_bound {n : ℕ} (u : Coord n → ℝ)
    (hu : MemLp u 2 volume) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ phi : Coord n → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      |∫ x, u x*phi x| ≤ C*Real.sqrt (∫ x, (phi x)^2)) :
    ‖hu.toLp u‖ ≤ C := by
  let U := hu.toLp u
  have hclosed : IsClosed {v : RealEuclideanL2 n | |inner ℝ U v| ≤ C*‖v‖} :=
    isClosed_le ((continuous_const.inner continuous_id).abs) (continuous_const.mul continuous_norm)
  have hsub : {v : RealEuclideanL2 n | ∃ phi : Coord n → ℝ,
      (v : Coord n → ℝ) =ᵐ[volume] phi ∧ HasCompactSupport phi ∧ ContDiff ℝ ∞ phi} ⊆
      {v : RealEuclideanL2 n | |inner ℝ U v| ≤ C*‖v‖} := by
    rintro v ⟨phi,hv,hc,hp⟩
    have hm := real_compact_continuous_memLp phi hp.continuous hc
    have he : v=hm.toLp phi := Lp.ext (hv.trans hm.coeFn_toLp.symm)
    rw [he]
    change |inner ℝ (hu.toLp u) (hm.toLp phi)| ≤ C*‖hm.toLp phi‖
    rw [real_toLp_inner]
    have hn := real_toLp_norm_sq phi hm
    have hs : Real.sqrt (∫ x, (phi x)^2)=‖hm.toLp phi‖ := by
      rw [← hn,Real.sqrt_sq (norm_nonneg _)]
    simpa only [hs] using hb phi hp hc
  have hall : ∀ v : RealEuclideanL2 n, |inner ℝ U v| ≤ C*‖v‖ := by
    intro v
    apply (closure_minimal hsub hclosed)
    exact (Lp.dense_hasCompactSupport_contDiff (μ := (volume : Measure (Coord n))) (F := ℝ)
      (by norm_num : (2:ENNReal) ≠ ⊤)) v
  have h := hall U
  rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at h
  change ‖U‖ ≤ C
  nlinarith [norm_nonneg U]

end
end Yau

end OAI
