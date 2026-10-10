import OAI.Analysis.NumericalRange.Main

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [DecidableEq n] [Nonempty n] in
lemma metric_congruence_mono [DecidableEq n] [Nonempty n] {A B : Matrix n n ℂ} (h : A ≤ B)
    (R : Matrix n n ℂ) : Rᴴ*A*R ≤ Rᴴ*B*R := by
  have hp := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)).conjTranspose_mul_mul_same R
  apply sub_nonneg.mp
  have he : Rᴴ*(B-A)*R = Rᴴ*B*R-Rᴴ*A*R := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [he] at hp
  exact hp.nonneg

omit [Nonempty n] in
lemma metric_gram_le_norm_sq [Nonempty n] (R : Matrix n n ℂ) :
    Rᴴ*R ≤ ‖R‖^2 • (1 : Matrix n n ℂ) := by
  simpa only [Matrix.star_eq_conjTranspose, Algebra.algebraMap_eq_smul_one] using
    (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := R))

theorem similarity_normalized_metric_feasible {T R : Matrix n n ℂ}
    (hR : IsUnit R) (hc : ‖R*T*R⁻¹‖ ≤ 1) :
    MetricFeasible T ((‖R‖*‖R⁻¹‖)^2) (‖R⁻¹‖^2 • (Rᴴ*R)) := by
  have hi : R⁻¹*R = 1 :=
    Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det R).mp hR)
  have hscale : 0 ≤ ‖R⁻¹‖^2 := sq_nonneg _
  have hlo := metric_congruence_mono (metric_gram_le_norm_sq R⁻¹) R
  have hgram : Rᴴ*(R⁻¹ᴴ*R⁻¹)*R = 1 := by
    calc
      _ = (R⁻¹*R)ᴴ*(R⁻¹*R) := by
        simp only [Matrix.conjTranspose_mul]
        noncomm_ring
      _ = 1 := by rw [hi]; simp
  have hlo' : 1 ≤ ‖R⁻¹‖^2 • (Rᴴ*R) := by
    simpa only [hgram, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] using hlo
  have hupper := smul_le_smul_of_nonneg_left (metric_gram_le_norm_sq R) hscale
  have hupper' : ‖R⁻¹‖^2 • (Rᴴ*R) ≤
      algebraMap ℝ (Matrix n n ℂ) ((‖R‖*‖R⁻¹‖)^2) := by
    rw [Algebra.algebraMap_eq_smul_one]
    have he : ‖R⁻¹‖^2 • (‖R‖^2 • (1 : Matrix n n ℂ)) =
        (‖R‖*‖R⁻¹‖)^2 • (1 : Matrix n n ℂ) := by
      rw [smul_smul]
      congr 1
      ring
    rwa [he] at hupper
  let D := R*T*R⁻¹
  have hDR : D*R = R*T := by
    dsimp [D]
    rw [Matrix.mul_assoc, hi, Matrix.mul_one]
  have hstein := metric_congruence_mono ((matrix_contractivity_iff D).mpr hc) R
  have he : Rᴴ*(Dᴴ*D)*R = Tᴴ*(Rᴴ*R)*T := by
    calc
      _ = (D*R)ᴴ*(D*R) := by
        simp only [Matrix.conjTranspose_mul]
        noncomm_ring
      _ = (R*T)ᴴ*(R*T) := by rw [hDR]
      _ = _ := by simp only [Matrix.conjTranspose_mul]; noncomm_ring
  have hstein' : Tᴴ*(Rᴴ*R)*T ≤ Rᴴ*R := by
    simpa only [he, Matrix.mul_one] using hstein
  refine ⟨hlo', hupper', ?_⟩
  simpa only [Matrix.mul_smul, Matrix.smul_mul] using
    (smul_le_smul_of_nonneg_left hstein' hscale)

theorem optimal_metric_sqrt_le_similarity {T H : Matrix n n ℂ} {τ : ℝ}
    (hf : MetricFeasible T τ H)
    (hm : ∀ s J, MetricFeasible T s J → τ ≤ s)
    {R : Matrix n n ℂ} (hR : IsUnit R) (hc : ‖R*T*R⁻¹‖ ≤ 1) :
    Real.sqrt τ ≤ ‖R‖*‖R⁻¹‖ := by
  have hmin := hm _ _ (similarity_normalized_metric_feasible hR hc)
  have ht : 0 ≤ τ := zero_le_one.trans hf.one_le
  have hs := Real.sq_sqrt ht
  have hr : 0 ≤ ‖R‖*‖R⁻¹‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [Real.sqrt_nonneg τ]

theorem optimal_metric_similarity_minimal {T H : Matrix n n ℂ} {τ : ℝ}
    (hf : MetricFeasible T τ H) (hp : H.PosDef)
    (hm : ∀ s J, MetricFeasible T s J → τ ≤ s) :
    IsUnit (CFC.sqrt H) ∧ ‖CFC.sqrt H*T*(CFC.sqrt H)⁻¹‖ ≤ 1 ∧
      ∀ R : Matrix n n ℂ, IsUnit R → ‖R*T*R⁻¹‖ ≤ 1 →
        ‖CFC.sqrt H‖*‖(CFC.sqrt H)⁻¹‖ ≤ ‖R‖*‖R⁻¹‖ := by
  refine ⟨metric_sqrt_isUnit hp, metric_similarity_contraction hf hp, ?_⟩
  intro R hR hc
  exact (metric_condition_estimate hf hp).trans
    (optimal_metric_sqrt_le_similarity hf hm hR hc)

theorem optimal_metric_condition_eq_from_minimality
    {T H : Matrix n n ℂ} {τ : ℝ}
    (hf : MetricFeasible T τ H) (hp : H.PosDef)
    (hm : ∀ s J, MetricFeasible T s J → τ ≤ s) :
    ‖CFC.sqrt H‖*‖(CFC.sqrt H)⁻¹‖ = Real.sqrt τ := by
  exact le_antisymm (metric_condition_estimate hf hp)
    (optimal_metric_sqrt_le_similarity hf hm (metric_sqrt_isUnit hp)
      (metric_similarity_contraction hf hp))

theorem optimal_metric_similarity_exact {T H : Matrix n n ℂ} {τ : ℝ}
    (hf : MetricFeasible T τ H) (hp : H.PosDef)
    (hm : ∀ s J, MetricFeasible T s J → τ ≤ s) :
    ‖CFC.sqrt H‖*‖(CFC.sqrt H)⁻¹‖ = Real.sqrt τ ∧
    IsUnit (CFC.sqrt H) ∧ ‖CFC.sqrt H*T*(CFC.sqrt H)⁻¹‖ ≤ 1 ∧
      ∀ R : Matrix n n ℂ, IsUnit R → ‖R*T*R⁻¹‖ ≤ 1 →
        Real.sqrt τ ≤ ‖R‖*‖R⁻¹‖ := by
  refine ⟨optimal_metric_condition_eq_from_minimality hf hp hm,
    metric_sqrt_isUnit hp, metric_similarity_contraction hf hp, ?_⟩
  intro R hR hc
  exact optimal_metric_sqrt_le_similarity hf hm hR hc

theorem optimal_metric_similarity_isLeast {T H : Matrix n n ℂ} {τ : ℝ}
    (hf : MetricFeasible T τ H) (hp : H.PosDef)
    (hm : ∀ s J, MetricFeasible T s J → τ ≤ s) :
    IsLeast {c : ℝ | ∃ R : Matrix n n ℂ, IsUnit R ∧
      ‖R*T*R⁻¹‖ ≤ 1 ∧ ‖R‖*‖R⁻¹‖ = c} (Real.sqrt τ) := by
  constructor
  · exact ⟨CFC.sqrt H, metric_sqrt_isUnit hp,
      metric_similarity_contraction hf hp,
      optimal_metric_condition_eq_from_minimality hf hp hm⟩
  · intro c hc
    obtain ⟨R, hR, hcontract, heq⟩ := hc
    rw [← heq]
    exact optimal_metric_sqrt_le_similarity hf hm hR hcontract

end CompleteCrouzeix

end

end OAI
