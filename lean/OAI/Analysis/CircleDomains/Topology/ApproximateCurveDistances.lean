import OAI.Analysis.CircleDomains.Sobolev.ApproximateCurveDerivative

namespace OAI

/-! Upper and lower distance control for plane curves on differentiability pieces. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma approximate_curve_lower_distance {γ : ℝ → ℂ} {A : ℝ →L[ℝ] ℂ}
    {S : Set ℝ} {δ : ℝ≥0} (ha : ApproximatesLinearOn γ A S δ) :
    ∀ x ∈ S, ∀ y ∈ S,
      (Real.toNNReal (‖A‖-(δ:ℝ)) : ℝ) * dist x y ≤ dist (γ x) (γ y) := by
  intro x hx y hy
  have hr := ha x hx y hy
  have ht : ‖A (x-y)‖ ≤ ‖γ x-γ y‖ + ‖γ x-γ y-A (x-y)‖ := by
    have he : A (x-y) = (γ x-γ y)-(γ x-γ y-A (x-y)) := by abel
    nth_rw 1 [he]
    exact norm_sub_le _ _
  rw [norm_real_clm_apply] at ht
  rw [Real.dist_eq, dist_eq_norm]
  by_cases hp : 0 ≤ ‖A‖-(δ:ℝ)
  · rw [Real.coe_toNNReal _ hp]
    rw [Real.norm_eq_abs] at hr
    nlinarith
  · rw [Real.toNNReal_of_nonpos (le_of_not_ge hp), NNReal.coe_zero, zero_mul]
    exact norm_nonneg _

lemma differentiable_curve_distance_partition {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    {S : Set ℝ} (hS : MeasurableSet S) (hd : ∀ x ∈ S, HasFDerivWithinAt γ (d x) S x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (B : ℕ → Set ℝ) (K k : ℕ → ℝ≥0),
      (∀ n, MeasurableSet (B n)) ∧ Pairwise (Disjoint on B) ∧ (⋃ n, B n) = S ∧
      (∀ n, LipschitzOnWith (K n) γ (B n)) ∧
      (∀ n x, x ∈ B n → ∀ y ∈ B n, (k n : ℝ)*dist x y ≤ dist (γ x) (γ y)) ∧
      ∀ n, ∀ᵐ x ∂volume.restrict (B n),
        (K n : ℝ) ≤ ‖d x‖+ε ∧ ‖d x‖ ≤ (k n : ℝ)+ε := by
  let δ : ℝ≥0 := ⟨ε/2, (half_pos hε).le⟩
  obtain ⟨t, A, htDisj, htMeas, htCover, htApprox, _⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt γ S d
      hd (fun _ => δ)
      (fun _ => ne_of_gt (show 0 < δ by exact half_pos hε))
  let B : ℕ → Set ℝ := fun n => S ∩ t n
  let K : ℕ → ℝ≥0 := fun n => ‖A n‖₊+δ
  let k : ℕ → ℝ≥0 := fun n => Real.toNNReal (‖A n‖-(δ:ℝ))
  have hB (n : ℕ) : MeasurableSet (B n) := hS.inter (htMeas n)
  refine ⟨B, K, k, hB, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j hij => (htDisj hij).mono inter_subset_right inter_subset_right
  · simp only [B, ← inter_iUnion, inter_eq_left.mpr htCover]
  · intro n
    exact lipschitzOnWith_iff_restrict.mpr (htApprox n).lipschitz
  · intro n
    exact approximate_curve_lower_distance (htApprox n)
  · intro n
    filter_upwards [ae_restrict_of_ae (ae_curve_derivative_sub_le (htApprox n)),
      ae_restrict_mem (hB n)] with x hx hxB
    have hnorm := hx hxB ((hd x hxB.1).mono inter_subset_left)
    have h1 := norm_sub_norm_le (A n) (d x)
    have h2 := norm_sub_norm_le (d x) (A n)
    rw [norm_sub_rev] at h1
    have hk : ‖A n‖-(δ:ℝ) ≤ (k n : ℝ) := Real.le_coe_toNNReal _
    change ‖A n‖+(ε/2) ≤ ‖d x‖+ε ∧ ‖d x‖ ≤ (k n : ℝ)+ε
    change ‖d x-A n‖ ≤ ε/2 at hnorm
    change ‖A n‖-ε/2 ≤ (k n : ℝ) at hk
    constructor <;> linarith

end CircleDomainRigidity

end

end OAI
