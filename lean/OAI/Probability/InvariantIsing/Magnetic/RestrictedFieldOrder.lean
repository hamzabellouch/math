import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldRecursion

namespace OAI

/-! Inclusion and exact bias transport through the constrained Gaussian
recursion, before normalizing per cavity spin. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem restrictedFieldRecursion_mono {N : ℕ} (hN : 0 < N)
    (S T : Finset (Spin N)) (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i) (z : Fin N → ℝ) :
    restrictedFieldRecursion S n b v z ≤ restrictedFieldRecursion T n b v z := by
  induction n generalizing b v z with
  | zero => exact restrictedSpinLog_mono hS hST (fun _ _ => le_rfl)
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    change logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
      (fun w => restrictedFieldRecursion S n bs vs (z + w)) ≤
      logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
      (fun w => restrictedFieldRecursion T n bs vs (z + w))
    exact logMean_mono _ (hb 0 (by omega))
      (integrable_exp_restrictedFieldRecursion hN S hS n bs vs hbs (v 0) (b 0) z)
      (integrable_exp_restrictedFieldRecursion hN T hT n bs vs hbs (v 0) (b 0) z)
      (fun w => ih bs vs hbs (z + w))

theorem constrainedBlockValue_mono {N : ℕ} (hN : 0 < N)
    (S T : Finset (Spin N)) (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T)
    (h : FieldStep) : constrainedBlockValue S h ≤ constrainedBlockValue T h := by
  unfold constrainedBlockValue
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono (constrainedBlockValue_root_integrable hN S hS h)
    (constrainedBlockValue_root_integrable hN T hT h)
  intro z
  exact restrictedFieldRecursion_mono hN S T hS hT hST _ _ _
    (fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1) z

theorem restrictedFieldRecursion_group_bias {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (bias : A → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i) (z : Fin N → ℝ) :
    restrictedFieldRecursion (spinGroupSlice group k) n b v (z + fun i => bias (group i)) =
      restrictedFieldRecursion (spinGroupSlice group k) n b v z +
        spinGroupFieldConstant group k bias := by
  induction n generalizing b v z with
  | zero => exact restrictedFieldTerminal_group_bias group k hk bias z
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    change logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
      (fun w => restrictedFieldRecursion (spinGroupSlice group k) n bs vs
        ((z + fun i => bias (group i)) + w)) =
      logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))
        (fun w => restrictedFieldRecursion (spinGroupSlice group k) n bs vs (z + w)) + _
    have he : (fun w : Fin N → ℝ => restrictedFieldRecursion (spinGroupSlice group k) n bs vs
        ((z + fun i => bias (group i)) + w)) =
        fun w => spinGroupFieldConstant group k bias +
          restrictedFieldRecursion (spinGroupSlice group k) n bs vs (z + w) := by
      funext w
      have hz : (z + fun i => bias (group i)) + w = (z + w) + fun i => bias (group i) := by abel
      rw [hz, ih bs vs hbs]
      ring
    rw [he, logMean_const_add _ (hb 0 (by omega)).ne'
      (integrable_exp_restrictedFieldRecursion hN _ (spinGroupSlice_nonempty group k hk)
        n bs vs hbs (v 0) (b 0) z)]
    ring

end InvariantIsing

end

end OAI
