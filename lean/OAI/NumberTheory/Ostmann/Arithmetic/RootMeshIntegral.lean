import OAI.NumberTheory.Ostmann.Arithmetic.CommonRootMesh

namespace OAI

/-! # Reassembling root cells into the original real integral -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

theorem rootMeshWeight_integral {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (S : Finset ℝ)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y)
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (ρ : ℝ → ℂ) (hρ : ContinuousOn ρ (Set.Icc (s 0) (s N))) :
    IntervalIntegrable (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) * ρ y)
      volume (s 0) (s N) ∧
    (∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
      rootMeshWeight F w s j y * ρ y) =
      ∫ y in Set.Ioc (s 0) (s N),
        w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) * ρ y := by
  let f := fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) * ρ y
  have heq (j : ℕ) (hj : j < N) (y : ℝ) (hy : y ∈ Set.Ioo (s j) (s (j + 1))) :
      rootMeshWeight F w s j y * ρ y = f y := by
    rw [← rootMeshWeight_eq F w S hconst s N hfree j hj y hy]
  have hc (j : ℕ) (hj : j < N) :
      IntervalIntegrable (fun y => rootMeshWeight F w s j y * ρ y) volume (s j) (s (j + 1)) := by
    apply ((rootMeshWeight_continuous F w s j).continuousOn.mul (hρ.mono ?_)).intervalIntegrable_of_Icc
      (hs (Nat.le_succ _))
    intro y hy
    exact ⟨(hs (Nat.zero_le _)).trans hy.1, hy.2.trans (hs (by omega))⟩
  have hf (j : ℕ) (hj : j < N) : IntervalIntegrable f volume (s j) (s (j + 1)) := by
    apply (hc j hj).congr_uIoo
    rw [Set.uIoo_of_le (hs (Nat.le_succ _))]
    exact heq j hj
  refine ⟨IntervalIntegrable.trans_iterate hf, ?_⟩
  have heqI (j : ℕ) (hj : j < N) :
      (∫ y in Set.Ioc (s j) (s (j + 1)), rootMeshWeight F w s j y * ρ y) =
        ∫ y in (s j)..(s (j + 1)), f y := by
    rw [← intervalIntegral.integral_of_le (hs (Nat.le_succ _))]
    exact intervalIntegral.integral_congr_Ioo_of_le (hs (Nat.le_succ _)) (heq j hj)
  calc
    _ = ∑ j ∈ Finset.range N, ∫ y in (s j)..(s (j + 1)), f y := by
      apply Finset.sum_congr rfl
      intro j hj
      exact heqI j (Finset.mem_range.mp hj)
    _ = ∫ y in (s 0)..(s N), f y := intervalIntegral.sum_integral_adjacent_intervals hf
    _ = _ := intervalIntegral.integral_of_le (hs (Nat.zero_le _))

/-- No root-dependent main term survives the partition. The full density
and the sharp real gate remain inside one integral. -/
theorem PublishedProgressionInput.common_root_prime_integral (P : PublishedProgressionInput)
    (S : Finset ℝ) (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (hu : 1 ≤ s 0) (hshort : s N ≤ s 0 + 1)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (w : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, ‖w x‖ ≤ C)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) :
    ‖complexPrimeInterval q a (s 0) (s N)
        (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
      ∫ y in Set.Ioc (s 0) (s N), w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) *
        (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N,
        (‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F *
          (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
            Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) +
          2 * C * smoothPolynomialBudget F * Real.exp (-(s j))) := by
  have h := P.common_root_mesh_prime_comparison S s hs N hfree hQ hq hqQ ha hu hshort F hroots
    w C hC hw hconst
  have hρ : ContinuousOn (fun y => (selectedPrimeLogDensity P Q q a y : ℂ)) (Set.Icc (s 0) (s N)) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_primeLogDensity _ _ _ (by linarith))
  rwa [(rootMeshWeight_integral F w S hconst s hs N hfree _ hρ).2] at h

theorem common_root_integer_integral
    (S : Finset ℝ) (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (q a : ℕ) (hq : 0 < q) (G : ℝ) {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (w : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, ‖w x‖ ≤ C)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) :
    ‖complexIntegerInterval q a (s 0) (s N) G
        (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
      ∫ y in Set.Ioc (s 0) (s N), w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) *
        (integerLogDensity q G y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N,
        (‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F *
          (2 * Real.exp (-G)) + 2 * C * smoothPolynomialBudget F * Real.exp (-G)) := by
  have h := common_root_mesh_integer_comparison S s hs N hfree q a hq G F hroots w C hC hw hconst
  have hρ : ContinuousOn (fun y => (integerLogDensity q G y : ℂ)) (Set.Icc (s 0) (s N)) :=
    (Complex.continuous_ofReal.comp (continuous_integerLogDensity q G)).continuousOn
  rwa [(rootMeshWeight_integral F w S hconst s hs N hfree _ hρ).2] at h

end Ostmann

end OAI
