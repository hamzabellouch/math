import OAI.Probability.InvariantIsing.Gaussian.GaussianOperatorMean

namespace OAI

/-! Exact variance gives the second-moment upper bound needed for Gaussian Gram tails. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

theorem gaussianPatternSingularMax_mean_le (N m : ℕ) :
    (∫ z, gaussianPatternSingularMax (N := N) (m := m) z ∂stdGaussian _) ≤
      Real.sqrt N + Real.sqrt m := by
  by_cases hN : N = 0
  · subst N
    have hz (z : EuclideanSpace ℝ (Fin 0 × Fin m)) : gaussianPatternSingularMax z = 0 := by
      unfold gaussianPatternSingularMax
      rw [Subsingleton.elim (gaussianPatternEuclideanOperator z) 0,norm_zero]
    simp only [hz,integral_zero,Nat.cast_zero,Real.sqrt_zero,zero_add]
    exact Real.sqrt_nonneg _
  by_cases hm : m = 0
  · subst m
    have hz (z : EuclideanSpace ℝ (Fin N × Fin 0)) : gaussianPatternSingularMax z = 0 := by
      unfold gaussianPatternSingularMax
      rw [Subsingleton.elim (gaussianPatternEuclideanOperator z) 0,norm_zero]
    simp only [hz,integral_zero,Nat.cast_zero,Real.sqrt_zero,add_zero]
    exact Real.sqrt_nonneg _
  exact gaussianPatternSingularMax_mean_le_pos (Nat.pos_of_ne_zero hN) (Nat.pos_of_ne_zero hm)

lemma gaussianPatternSingularMax_mean_nonneg (N m : ℕ) :
    0 ≤ ∫ z, gaussianPatternSingularMax (N := N) (m := m) z ∂stdGaussian _ :=
  integral_nonneg (fun _ => norm_nonneg _)

lemma gaussianPatternSingularMax_sq_integral_le {N m : ℕ} (hN : 0 < N) (hm : 0 < m) :
    (∫ z, (gaussianPatternSingularMax (N := N) (m := m) z)^2 ∂stdGaussian _) ≤
      1+(Real.sqrt N+Real.sqrt m)^2 := by
  have hmem := finiteGaussian_lipschitz_memLp_two (gaussianPatternSingularMax_lipschitz N m)
  have hv := gaussianPatternSingularMax_variance N m
  rw [variance_eq_sub hmem] at hv
  have hn := gaussianPatternSingularMax_mean_nonneg N m
  have hb := gaussianPatternSingularMax_mean_le_pos hN hm
  have hs := sq_le_sq₀ hn (by positivity : 0 ≤ Real.sqrt N+Real.sqrt m) |>.2 hb
  change (∫ z, (gaussianPatternSingularMax z)^2 ∂stdGaussian _) - _ ≤ 1 at hv
  linarith

lemma gaussianPatternSingularMax_upper_tail {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → EuclideanSpace ℝ (Fin N × Fin m)) (hZ : HasLaw Z (stdGaussian _) P)
    (r : ℝ) (hr : 0 < r) :
    P {ω | Real.sqrt N+Real.sqrt m+r ≤ gaussianPatternSingularMax (Z ω)} ≤
      ENNReal.ofReal (1/r^2) := by
  have hb := gaussianPatternSingularMax_mean_le_pos hN hm
  have hsub : {ω | Real.sqrt N+Real.sqrt m+r ≤ gaussianPatternSingularMax (Z ω)} ⊆
      {ω | r ≤ |gaussianPatternSingularMax (Z ω) -
        (∫ z : EuclideanSpace ℝ (Fin N × Fin m), gaussianPatternSingularMax z ∂stdGaussian _)|} := by
    intro ω hω
    have hr' : r ≤ gaussianPatternSingularMax (Z ω) -
        (∫ z : EuclideanSpace ℝ (Fin N × Fin m), gaussianPatternSingularMax z ∂stdGaussian _) := by
      change Real.sqrt N+Real.sqrt m+r ≤ gaussianPatternSingularMax (Z ω) at hω
      linarith
    exact hr'.trans (le_abs_self _)
  refine (measure_mono hsub).trans ?_
  simpa only [div_one,one_pow,one_mul] using
    finiteGaussian_lipschitz_tail (gaussianPatternSingularMax_lipschitz N m) P Z hZ 1 r
      zero_lt_one hr

end InvariantIsing

end

end OAI
