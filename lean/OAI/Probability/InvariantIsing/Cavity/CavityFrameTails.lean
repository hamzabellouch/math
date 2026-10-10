import OAI.Probability.InvariantIsing.Cavity.CavityFrameMoments

namespace OAI

/-! Removing bounded radial cutoffs from fresh-frame Gibbs averages. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace InvariantIsing

lemma cavity_radial_defect_bound {q : ℕ} (B : ℝ) (hB : 0 < B)
    (φ : EuclideanSpace ℝ (Fin q) → ℝ)
    (hφ : ∀ y, 0 ≤ φ y ∧ φ y ≤ 1)
    (hzero : ∀ y, ‖y‖ ≤ B → φ y = 0) (y : EuclideanSpace ℝ (Fin q)) :
    φ y ≤ ‖y‖ ^ 2 / B ^ 2 := by
  by_cases hy : ‖y‖ ≤ B
  · rw [hzero y hy]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  · apply (hφ y).2.trans
    apply (le_div_iff₀ (sq_pos_of_pos hB)).mpr
    nlinarith [norm_nonneg y, lt_of_not_ge hy]

theorem cavity_frame_mixture_cutoff_error {n q : ℕ} {X : Type*} [Fintype X]
    (hn : 0 < n) (μ : Measure (Orthogonal n))
    [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    (v : X → EuclideanSpace ℝ (Fin n)) (u : Fin q → EuclideanSpace ℝ (Fin n))
    (hu : ∀ j, ‖u j‖ = 1) (L : ℝ) (hv : ∀ x, ‖v x‖ ^ 2 ≤ L * n)
    (B : ℝ) (hB : 0 < B) (φ : EuclideanSpace ℝ (Fin q) → ℝ)
    (hφc : Continuous φ) (hφ : ∀ y, 0 ≤ φ y ∧ φ y ≤ 1)
    (hzero : ∀ y, ‖y‖ ≤ B → φ y = 0) :
    (∫ U, ∑ x, w x * φ (cavityHaarProjections (v x) u U) ∂μ) ≤ q * L / B ^ 2 := by
  have hb (U : Orthogonal n) :
      (∑ x, w x * φ (cavityHaarProjections (v x) u U)) ≤
        (∑ x, w x * ‖cavityHaarProjections (v x) u U‖ ^ 2) / B ^ 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum (fun x _ => by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
        (cavity_radial_defect_bound B hB φ hφ hzero (cavityHaarProjections (v x) u U)) (hw x))
  have hi : Integrable (fun U => ∑ x, w x * ‖cavityHaarProjections (v x) u U‖ ^ 2) μ :=
    integrable_finsetSum _ (fun x _ =>
      (integrable_cavityHaarProjections_power μ (v x) u 2).const_mul (w x))
  have hli : Integrable (fun U => ∑ x, w x * φ (cavityHaarProjections (v x) u U)) μ := by
    apply integrable_finsetSum
    intro x _
    apply Integrable.const_mul
    apply Integrable.of_bound
      (hφc.comp (continuous_cavityHaarProjections (v x) u)).aestronglyMeasurable 1
    exact ae_of_all _ (fun U => by
      change |φ (cavityHaarProjections (v x) u U)| ≤ 1
      rw [abs_of_nonneg (hφ _).1]
      exact (hφ _).2)
  have hm : (∫ U, ∑ x, w x * ‖cavityHaarProjections (v x) u U‖ ^ 2 ∂μ) ≤ q * L := by
    simpa only [zero_add, Nat.reduceAdd, Nat.mul_one, pow_one,
      cavityGaussianAbsMoment_two, mul_one] using
      cavity_frame_mixture_even_moment hn μ w hw hsum v u hu 0 L hv
  calc
    _ ≤ ∫ U, (∑ x, w x * ‖cavityHaarProjections (v x) u U‖ ^ 2) / B ^ 2 ∂μ :=
      integral_mono hli (hi.div_const _) hb
    _ = (∫ U, ∑ x, w x * ‖cavityHaarProjections (v x) u U‖ ^ 2 ∂μ) / B ^ 2 :=
      integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right hm (sq_nonneg _)

end InvariantIsing

end

end OAI
