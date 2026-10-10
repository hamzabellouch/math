import OAI.Probability.InvariantIsing.Magnetic.RestrictedPairRecursion

namespace OAI

/-! Nonnegativity and conditional Jensen monotonicity of the actual
constrained block's coordinate overlap levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma restrictedPairCoordinateMean_nonneg {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (i : Fin (n + 1)) (j : Fin N) (z : Fin N → ℝ) :
    0 ≤ restrictedPairCoordinateMean hN S hS n b v hb i j z := by
  induction n generalizing b v z with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    rw [hi, restrictedPairCoordinateMean_zero]
    positivity
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [restrictedPairCoordinateMean_zero]
      positivity
    · rw [restrictedPairCoordinateMean_succ]
      exact integral_nonneg (fun y => ih _ _ _ k y)

lemma restrictedPairCoordinateMean_monotone {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (j : Fin N) (z : Fin N → ℝ) :
    Monotone (fun i => restrictedPairCoordinateMean hN S hS n b v hb i j z) := by
  induction n generalizing b v z with
  | zero =>
    intro i k _
    have hik : i = k := Fin.ext (by omega)
    subst k
    exact le_rfl
  | succ n ih =>
    let bs := fun k => b (k + 1)
    let vs := fun k => v (k + 1)
    have hbs : ∀ k < n, 0 < bs k := fun k hk => hb (k + 1) (by omega)
    let K := vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion S n bs vs)
      (restrictedFieldRecursion_regular hN S hS n bs vs hbs).1
    let M := restrictedCoordinateMean hN S hS n bs vs hbs j
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [Fin.castSucc_zero, restrictedPairCoordinateMean_zero,
        restrictedCoordinateMean_succ, restrictedPairCoordinateMean_succ]
      simp_rw [restrictedPairCoordinateMean_zero]
      have hm : MemLp M 2 (K z) := MemLp.of_bound
        (measurable_restrictedCoordinateMean hN S hS n bs vs hbs j).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun y => by
          simpa only [Real.norm_eq_abs] using restrictedCoordinateMean_bound hN S hS n bs vs hbs j y))
      have hv := variance_nonneg M (K z)
      rw [variance_eq_sub hm] at hv
      exact sub_nonneg.mp hv
    · change restrictedPairCoordinateMean hN S hS (n + 1) b v hb k.castSucc.succ j z ≤
        restrictedPairCoordinateMean hN S hS (n + 1) b v hb k.succ.succ j z
      rw [restrictedPairCoordinateMean_succ, restrictedPairCoordinateMean_succ]
      apply integral_mono
        (integrable_restrictedPairCoordinateMean hN S hS n bs vs hbs k.castSucc j (K z))
        (integrable_restrictedPairCoordinateMean hN S hS n bs vs hbs k.succ j (K z))
      intro y
      exact ih bs vs hbs y (by change k.val ≤ k.val + 1; omega)

end InvariantIsing

end

end OAI
