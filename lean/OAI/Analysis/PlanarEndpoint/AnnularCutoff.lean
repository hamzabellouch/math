import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphTree

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
namespace PlanarEndpoint

def outerBump : ContDiffBump (0 : Plane) := ⟨2,4,by norm_num,by norm_num⟩
def innerBump : ContDiffBump (0 : Plane) := ⟨1/4,1,by norm_num,by norm_num⟩
def annularCutoff (ξ : Plane) : ℂ := ((outerBump ξ-innerBump ξ : ℝ) : ℂ)

lemma annularCutoff_smooth : ContDiff ℝ ∞ annularCutoff :=
  Complex.ofRealCLM.contDiff.comp (outerBump.contDiff.sub innerBump.contDiff)

lemma annularCutoff_zero_small {ξ : Plane} (hξ : ‖ξ‖ ≤ 1/4) : annularCutoff ξ=0 := by
  have hi := innerBump.one_of_mem_closedBall (x := ξ) (by simpa [innerBump] using hξ)
  have ho := outerBump.one_of_mem_closedBall (x := ξ) (by
    simpa [outerBump] using (show ‖ξ‖ ≤ 2 by linarith))
  simp [annularCutoff, hi, ho]

lemma annularCutoff_zero_large {ξ : Plane} (hξ : 4 ≤ ‖ξ‖) : annularCutoff ξ=0 := by
  have ho := outerBump.zero_of_le_dist (x := ξ) (by simpa [outerBump] using hξ)
  have hi := innerBump.zero_of_le_dist (x := ξ) (by
    simpa [innerBump] using (show 1 ≤ ‖ξ‖ by linarith))
  simp [annularCutoff, hi, ho]

lemma annularCutoff_support : ∀ ξ ∈ tsupport annularCutoff, 1/4 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 4 := by
  apply closure_minimal
  · intro ξ hξ
    have hn : annularCutoff ξ ≠ 0 := hξ
    exact ⟨le_of_not_gt (fun h => hn (annularCutoff_zero_small h.le)),
      le_of_not_gt (fun h => hn (annularCutoff_zero_large h.le))⟩
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)

lemma annularCutoff_compact : HasCompactSupport annularCutoff := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Plane) 4)
  intro ξ hξ
  exact annularCutoff_zero_large (le_of_lt (by simpa using hξ))

lemma annularCutoff_bound (ξ : Plane) : ‖annularCutoff ξ‖ ≤ 2 := by
  rw [annularCutoff, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [outerBump.nonneg (x := ξ), innerBump.le_one (x := ξ)],
    by linarith [outerBump.le_one (x := ξ), innerBump.nonneg (x := ξ)]⟩

lemma annularCutoff_one {ξ : Plane} (hξ : 1 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2) : annularCutoff ξ=1 := by
  have hi := innerBump.zero_of_le_dist (x := ξ) (by simpa [innerBump] using hξ.1)
  have ho := outerBump.one_of_mem_closedBall (x := ξ) (by simpa [outerBump] using hξ.2)
  simp [annularCutoff, hi, ho]

lemma dyadic_annular_cover {r : ℝ} (hr : 1 ≤ r) (n : ℕ) (hn : r < (2:ℝ)^n) :
    ∃ j < n, (2:ℝ)^j ≤ r ∧ r < (2:ℝ)^(j+1) := by
  obtain ⟨j,hj,hj'⟩ := exists_nat_pow_near hr (by norm_num : (1:ℝ)<2)
  refine ⟨j,?_,hj,hj'⟩
  by_contra hh
  have hnj : n ≤ j := by omega
  have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hnj
  linarith

lemma scaled_annularCutoff_one (j : ℕ) {ξ : Plane}
    (hξ : (2:ℝ)^j ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (2:ℝ)^(j+1)) :
    annularCutoff (((2:ℝ)^j)⁻¹ • ξ) = 1 := by
  apply annularCutoff_one
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [← div_eq_inv_mul, le_div_iff₀ (by positivity), div_le_iff₀ (by positivity)]
  simpa only [one_mul, pow_succ, mul_comm] using hξ

lemma graph_square_sum_of_shortTime {p : ℝ} (hp : 2 < p)
    (hshort : ShortTimeWeakEstimate (1/4) 4 p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x₀ : Plane) (T : Plane → ℝ) (w : Plane → ℂ)
      (hT : Measurable T) (hw : Measurable w) (hb : ∀ x, ‖w x‖ ≤ 1),
      (∀ x ∈ Metric.ball x₀ 1, T x ∈ Ico 0 1) → ∀ n : ℕ,
      (∑ j ∈ Finset.range n, ‖normalizedDyadicVector annularCutoff annularCutoff_smooth
        annularCutoff_compact j (volume.restrict (Metric.ball x₀ 1)) T w hT hw hb []‖^2) ≤ C :=
  graph_root_sum_of_shortTime (by norm_num) hp (by norm_num) hshort annularCutoff
    annularCutoff_smooth annularCutoff_compact annularCutoff_support 2 (by norm_num)
    annularCutoff_bound

end PlanarEndpoint
end

end OAI
