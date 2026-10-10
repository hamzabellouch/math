import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinBias
import OAI.Probability.InvariantIsing.Fields.VectorTransitionShift
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPairSpinKernel

namespace OAI

/-! Group-constant bias leaves every constrained continuation unchanged
once the same translation is applied to its current field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma restrictedTailSpinKernel_group_shift {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (bias : A → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i) (z : Fin N → ℝ) :
    restrictedTailSpinKernel hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      n b v hb (z + fun j => bias (group j)) =
    restrictedTailSpinKernel hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      n b v hb z := by
  induction n generalizing b v z with
  | zero => exact restrictedSpinKernel_group_bias group k hk bias z
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    let S := spinGroupSlice group k
    have hS := spinGroupSlice_nonempty group k hk
    let F := restrictedFieldRecursion S n bs vs
    have hF := restrictedFieldRecursion_regular hN S hS n bs vs hbs
    let κ := restrictedTailSpinKernel hN S hS n bs vs hbs
    let K := vectorGaussianTransition N (b 0) (v 0) F hF.1
    change (κ ∘ₖ K) (z + fun j => bias (group j)) = (κ ∘ₖ K) z
    ext T hT : 1
    rw [Kernel.comp_apply' _ _ _ hT, Kernel.comp_apply' _ _ _ hT,
      vectorGaussianTransition_shift hN (b 0) (v 0) F hF.1 hF.2
        (fun j => bias (group j)) (spinGroupFieldConstant group k bias)
        (fun y => restrictedFieldRecursion_group_bias hN group k hk bias n bs vs hbs y) z,
      lintegral_map (g := fun y : Fin N → ℝ => y + fun j => bias (group j))
        (κ.measurable_coe hT) (measurable_id.add_const _)]
    exact lintegral_congr (fun y => congrArg (fun μ : Measure (Spin N) => μ T)
      (ih bs vs hbs y))

lemma restrictedPairSpinKernel_group_shift {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (bias : A → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ j < n, 0 < b j)
    (i : Fin (n + 1)) (z : Fin N → ℝ) :
    restrictedPairSpinKernel hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      n b v hb i (z + fun j => bias (group j)) =
    restrictedPairSpinKernel hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      n b v hb i z := by
  let _ := restrictedSpinKernel_markov (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
  induction n generalizing b v z with
  | zero =>
    simp only [restrictedPairSpinKernel, Kernel.prod_apply, restrictedSpinKernel_group_bias group k hk bias]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [restrictedPairSpinKernel, Fin.cases_zero, Kernel.prod_apply,
        restrictedTailSpinKernel_group_shift hN group k hk bias]
    · let bs := fun j => b (j + 1)
      let vs := fun j => v (j + 1)
      have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j + 1) (by omega)
      let S := spinGroupSlice group k
      have hS := spinGroupSlice_nonempty group k hk
      let F := restrictedFieldRecursion S n bs vs
      have hF := restrictedFieldRecursion_regular hN S hS n bs vs hbs
      let κ := restrictedPairSpinKernel hN S hS n bs vs hbs j
      let K := vectorGaussianTransition N (b 0) (v 0) F hF.1
      change (κ ∘ₖ K) (z + fun j => bias (group j)) = (κ ∘ₖ K) z
      ext T hT : 1
      rw [Kernel.comp_apply' _ _ _ hT, Kernel.comp_apply' _ _ _ hT,
        vectorGaussianTransition_shift hN (b 0) (v 0) F hF.1 hF.2
          (fun j => bias (group j)) (spinGroupFieldConstant group k bias)
          (fun y => restrictedFieldRecursion_group_bias hN group k hk bias n bs vs hbs y) z,
        lintegral_map (g := fun y : Fin N → ℝ => y + fun j => bias (group j))
        (κ.measurable_coe hT) (measurable_id.add_const _)]
      exact lintegral_congr (fun y => congrArg (fun μ : Measure (Spin N × Spin N) => μ T)
        (ih bs vs hbs j y))

end InvariantIsing

end

end OAI
