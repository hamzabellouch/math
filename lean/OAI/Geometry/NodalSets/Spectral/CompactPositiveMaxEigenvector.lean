import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace OAI

namespace Yau.Analysis
open Filter Set Module.End
noncomputable section

theorem compact_positive_max_eigenvector {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [Nontrivial E]
    (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
    (hp : ∀ x, 0 ≤ inner ℝ (T x) x) (hT : T ≠ 0) :
    ∃ v : E, ‖v‖=1 ∧ T v=‖T‖ • v ∧
      inner ℝ (T v) v=‖T‖ ∧ ∀ x : E, inner ℝ (T x) x ≤ ‖T‖*‖x‖^2 := by
  have hn : 0 < ‖T‖ := norm_pos_iff.mpr hT
  have hspec : ‖T‖ ∈ spectrum ℝ T ∨ -‖T‖ ∈ spectrum ℝ T := by
    by_contra! h
    have h1 : ‖T‖ ∈ resolventSet ℝ T := by simpa only [spectrum,mem_compl_iff,not_not] using h.1
    have h2 : -‖T‖ ∈ resolventSet ℝ T := by simpa only [spectrum,mem_compl_iff,not_not] using h.2
    obtain ⟨c,hc0,hc⟩ := T.abs_rayleighQuotient_le_of_norm_mem_resolventSet h1 h2
    have hb : (⨆ x, |T.rayleighQuotient x|) ≤ ‖T‖-c := ciSup_le hc
    rw [← T.norm_eq_iSup_rayleighQuotient hs] at hb
    linarith
  have he : HasEigenvalue T.toLinearMap ‖T‖ := by
    rcases hspec with h | h
    · exact (hc.hasEigenvalue_iff_mem_spectrum hn.ne').mpr h
    · obtain ⟨v,hv⟩ := ((hc.hasEigenvalue_iff_mem_spectrum (neg_ne_zero.mpr hn.ne')).mpr h).exists_hasEigenvector
      have heq : T v = -‖T‖ • v := hv.apply_eq_smul
      have hh := hp v
      rw [heq,inner_smul_left_eq_smul,smul_eq_mul,real_inner_self_eq_norm_sq] at hh
      have hvpos : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv.2)
      nlinarith
  obtain ⟨v,hv⟩ := he.exists_hasEigenvector
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv.2
  let u := ‖v‖⁻¹ • v
  have hun : ‖u‖=1 := by
    simp only [u,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ hvnorm]
  have heq : T v=‖T‖ • v := hv.apply_eq_smul
  have hue : T u=‖T‖ • u := by
    dsimp [u]
    rw [map_smul,heq,smul_comm]
  refine ⟨u,hun,hue,?_,?_⟩
  · rw [hue,inner_smul_left_eq_smul,smul_eq_mul,real_inner_self_eq_norm_sq,hun]
    ring
  · intro x
    calc
      inner ℝ (T x) x ≤ ‖T x‖*‖x‖ := real_inner_le_norm _ _
      _ ≤ (‖T‖*‖x‖)*‖x‖ := mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg x)
      _ = ‖T‖*‖x‖^2 := by ring

end
end Yau.Analysis

end OAI
