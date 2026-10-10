import OAI.Probability.InvariantIsing.Cavity.CavityScalarSpin

namespace OAI

/-! Independent-site backward recursion after the ordinary cavity
residual is integrated. The residual contributes an additive constant. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

private lemma cavity_sum_logCosh_linearGrowth (N : ℕ) :
    HasLinearGrowth (fun z : Fin N → ℝ => ∑ i, Real.log (Real.cosh (z i))) := by
  refine ⟨0, N, le_rfl, Nat.cast_nonneg _, ?_⟩
  intro z
  simp only [zero_add]
  calc
    _ ≤ ∑ i, |Real.log (Real.cosh (z i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin N, ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (abs_log_cosh_le (z i)).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i)
    _ = _ := by simp

private lemma cavity_vector_recursion_const_add (N : ℕ) (hN : 0 < N)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i)
    (a : ℝ) (z : Fin N → ℝ) :
    cascadeRecursion n b (fun i => vectorGaussianLaw N (v i)) (fun _ p => p.1 + p.2)
      (fun y => a + ∑ i, Real.log (Real.cosh (y i))) z =
      a + cascadeRecursion n b (fun i => vectorGaussianLaw N (v i)) (fun _ p => p.1 + p.2)
        (fun y => ∑ i, Real.log (Real.cosh (y i))) z := by
  induction n generalizing b v z with
  | zero => rfl
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let F := cascadeRecursion n bs (fun i => vectorGaussianLaw N (vs i))
      (fun _ p => p.1 + p.2) (fun y => ∑ i, Real.log (Real.cosh (y i)))
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    have hm : Measurable F := measurable_cascadeRecursion n bs
      (fun i => vectorGaussianLaw N (vs i)) (fun _ => measurable_fst.add measurable_snd)
      (by fun_prop)
    have hg : HasLinearGrowth F := cascadeRecursion_linearGrowth n bs
      (fun i => vectorGaussianLaw N (vs i)) (fun i _ => vectorGaussianLaw_moments hN (vs i))
      (by fun_prop) (cavity_sum_logCosh_linearGrowth N) hbs
    have he : (fun g : Fin N → ℝ => cascadeRecursion n bs
        (fun i => vectorGaussianLaw N (vs i)) (fun _ p => p.1 + p.2)
        (fun y => a + ∑ i, Real.log (Real.cosh (y i))) (z + g)) =
        (fun g => a + F (z + g)) := by
      funext g
      exact ih bs vs hbs (z + g)
    change logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)) _ =
      a + logMean (b 0) (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)) _
    rw [he]
    exact logMean_const_add _ (hb 0 (by omega)).ne'
      (integrable_exp_of_linearGrowth _ (vectorGaussianLaw_moments hN (v 0))
        (hm.comp (measurable_const.add measurable_id)) (hg.add_left z) (b 0)) a

/-- The transformed cavity spin recursion separates into one identical
scalar recursion per cavity site; the ordinary residual is not a new
Poisson level. -/
theorem cavityResidualSpinLog_recursion (N : ℕ) (hN : 0 < N)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i)
    (r : ℝ≥0) (c : ℝ) (z : Fin N → ℝ) :
    cascadeRecursion n b (fun i => vectorGaussianLaw N (v i)) (fun _ p => p.1 + p.2)
      (cavityResidualSpinLog N r c) z =
      (N : ℝ) * (c + r) / 2 +
        ∑ i, cascadeRecursion n b (gaussianCascadeMarks v) (fun _ p => p.1 + p.2)
          (fun y => Real.log (Real.cosh y)) (z i) := by
  have ht : cavityResidualSpinLog N r c =
      (fun y => (N : ℝ) * (c + r) / 2 + ∑ i, Real.log (Real.cosh (y i))) := by
    funext y
    exact cavityResidualSpinLog_eq N r c y
  rw [ht, cavity_vector_recursion_const_add N hN n b v hb]
  congr 1
  simpa only [zero_add] using vectorCascade_logCosh_sum N n b v hb (fun _ => 0) z

end InvariantIsing

end

end OAI
