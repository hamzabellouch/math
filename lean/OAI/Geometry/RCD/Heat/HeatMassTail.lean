import OAI.Geometry.RCD.Heat.GaussianLinearGrowth

namespace OAI

/-! # Missing heat mass from a dyadic shell tail -/

open Set Metric MeasureTheory Function
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
/-- Integrating an upper bound over a subset costs at most the volume
of the larger finite-measure set. -/
theorem setIntegral_le_bound_mul_volume (μ : Measure X) {f : X → ℝ} {s t : Set X}
    (hsub : s ⊆ t) (ht : μ t ≠ ∞) (hi : IntegrableOn f s μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ.restrict s, f x ≤ C) :
    (∫ x in s, f x ∂μ) ≤ C * μ.real t := by
  have hs : μ s ≠ ∞ := ne_top_of_le_ne_top ht (measure_mono hsub)
  have hh := integral_mono_ae hi (integrableOn_const hs) hb
  have hv := mul_le_mul_of_nonneg_left (measureReal_mono hsub ht) hC
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul] at hh
  exact hh.trans (by simpa only [Measure.real, mul_comm] using hv)

/-- A summable shell majorant bounds exactly the heat mass outside a ball.
The prefix vanishes because its shells lie inside that ball. -/
theorem integral_outside_dyadic_ball_le_tail (μ : Measure X) (p : X)
    {r : ℝ} (hr : 0 < r) {f : X → ℝ} (hi : Integrable f μ)
    (hfinite : ∀ s, μ (ball p s) ≠ ∞)
    {W : ℕ → ℝ} (hW : ∀ j, 0 ≤ W j)
    (hbound : ∀ j, ∀ᵐ x ∂μ.restrict (dyadicShell p r j), f x ≤ W j)
    (hsum : Summable (fun j => W j * μ.real (ball p (2 ^ j * r)))) (N : ℕ) :
    (∫ x in (ball p (2 ^ N * r))ᶜ, f x ∂μ) ≤
      ∑' j, W (j + (N + 1)) * μ.real (ball p (2 ^ (j + (N + 1)) * r)) := by
  let S := fun j => dyadicShell p r j ∩ (ball p (2 ^ N * r))ᶜ
  have hS (j : ℕ) : MeasurableSet (S j) :=
    (measurableSet_dyadicShell p r j).inter measurableSet_ball.compl
  have hdis : Pairwise (Disjoint on S) := by
    intro i j hij
    exact (disjoint_disjointed (fun j : ℕ => ball p (2 ^ j * r)) hij).mono
      inter_subset_left inter_subset_left
  have hUnion : (⋃ j, S j) = (ball p (2 ^ N * r))ᶜ := by
    rw [show (⋃ j, S j) = (⋃ j, dyadicShell p r j) ∩ (ball p (2 ^ N * r))ᶜ by
      ext x; simp only [S, mem_iUnion, mem_inter_iff, exists_and_right]]
    rw [iUnion_dyadicShell p hr, univ_inter]
  have hpart := hasSum_integral_iUnion hS hdis hi.integrableOn
  rw [hUnion] at hpart
  have hzero (j : ℕ) (hj : j ≤ N) : S j = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hn⟩
    apply hn
    exact (ball_subset_ball (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hr.le))
      (dyadicShell_subset_ball p r j hx)
  have hpref : (∑ j ∈ Finset.range (N + 1), ∫ x in S j, f x ∂μ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hzero j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), setIntegral_empty]
  have he := hpart.summable.sum_add_tsum_nat_add (N + 1)
  rw [hpref, zero_add, hpart.tsum_eq] at he
  rw [← he]
  apply ((summable_nat_add_iff (N + 1)).mpr hpart.summable).tsum_le_tsum _
    ((summable_nat_add_iff (N + 1)).mpr hsum)
  intro j
  apply setIntegral_le_bound_mul_volume μ
    (inter_subset_left.trans (dyadicShell_subset_ball p r (j + (N + 1))))
    (hfinite _) hi.integrableOn (hW _)
  exact ae_restrict_of_ae_restrict_of_subset inter_subset_left (hbound _)

end RegularPointCoordinates

end

end OAI
