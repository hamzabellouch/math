import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import OAI.NumberTheory.Ostmann.QuadraticCenter.RealQuadraticPhase

namespace OAI

/-! # One differencing step for the actual quadratic exponential sum -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

private theorem real_part_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, Complex.add_re, ih]

private theorem norm_add_sq_real (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (w * conj z).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem sum_norm_sq_triangle (f : ℕ → ℂ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, f j‖ ^ 2 =
      (∑ j ∈ Finset.range N, ‖f j‖ ^ 2) +
        2 * ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range k, (f k * conj (f j)).re := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, norm_add_sq_real, ih]
    have hc : (f N * conj (∑ j ∈ Finset.range N, f j)).re =
        ∑ j ∈ Finset.range N, (f N * conj (f j)).re := by
      rw [map_sum, Finset.mul_sum, real_part_sum]
    simp only [Finset.sum_range_succ, hc]
    ring

private theorem triangle_sum_by_gap (F : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ j ∈ Finset.range k, F k j) =
      ∑ h ∈ Finset.range N, ∑ j ∈ Finset.range (N - (h + 1)), F (j + (h + 1)) j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun (z : Σ _ : ℕ, ℕ) _ => ⟨z.1 - z.2 - 1, z.2⟩)
  · intro z hz
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.mp hz
    apply Finset.mem_sigma.mpr
    simp only [Finset.mem_range] at hk hj ⊢
    constructor <;> omega
  · intro z hz w hw heq
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hl, hi⟩ := Finset.mem_sigma.mp hw
    simp only [Finset.mem_range] at hk hj hl hi
    have h₁ := congrArg (fun z : Σ _ : ℕ, ℕ => z.1) heq
    have h₂ := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) heq
    apply Sigma.ext
    · dsimp at h₁ h₂
      omega
    · exact heq_of_eq h₂
  · intro z hz
    obtain ⟨hh, hj⟩ := Finset.mem_sigma.mp hz
    simp only [Finset.mem_range] at hh hj
    refine ⟨⟨z.2 + (z.1 + 1), z.2⟩, Finset.mem_sigma.mpr ?_, ?_⟩
    · simp only [Finset.mem_range]
      constructor <;> omega
    · apply Sigma.ext
      · dsimp
        omega
      · rfl
  · intro z hz
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.mp hz
    simp only [Finset.mem_range] at hk hj
    dsimp
    congr 1
    omega

/-- The linear coefficient disappears after taking absolute values of the
shift correlations. No rational-approximation estimate is assumed here. -/
theorem quadratic_differencing_bound (α β : ℝ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, realQuadraticPhase α β j‖ ^ 2 ≤
      (N : ℝ) + 2 * ∑ h ∈ Finset.range N,
        ‖∑ j ∈ Finset.range (N - (h + 1)), realAdditivePhase (2 * α * (h + 1)) ^ j‖ := by
  rw [sum_norm_sq_triangle, triangle_sum_by_gap]
  have hdiag : (∑ j ∈ Finset.range N, ‖realQuadraticPhase α β j‖ ^ 2) = (N : ℝ) := by
    simp [realQuadraticPhase]
  rw [hdiag]
  gcongr with h hh
  rw [← real_part_sum]
  apply le_trans (Complex.re_le_norm _)
  rw [norm_quadratic_correlation_sum]
  simp only [Nat.cast_add, Nat.cast_one]
  exact le_rfl

end Ostmann

end OAI
