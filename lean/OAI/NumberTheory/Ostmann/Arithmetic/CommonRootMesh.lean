import OAI.NumberTheory.Ostmann.Arithmetic.RootCellPrimeComparison
import OAI.NumberTheory.Ostmann.Arithmetic.RootCellIntegerComparison

namespace OAI

/-! # One explicit root mesh for all residue classes -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

noncomputable def rootMeshWeight {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (s : ℕ → ℝ) (j : ℕ) (y : ℝ) : ℂ :=
  w (Real.exp ((s j + s (j + 1)) / 2)) * smoothPolynomialWeight F (Real.exp y)

theorem rootMeshWeight_continuous {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (s : ℕ → ℝ) (j : ℕ) : Continuous (rootMeshWeight F w s j) :=
  continuous_const.mul ((continuous_smoothPolynomialWeight F).comp Real.continuous_exp)

theorem rootMeshWeight_variation {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (S : Finset ℝ)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (s : ℕ → ℝ) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (j : ℕ) (hj : j < N) (r : ℕ → ℝ) (hr : Monotone r) (M : ℕ)
    (hr0 : r 0 = s j) (hrM : r M = s (j + 1)) :
    discreteVariation (fun l => rootMeshWeight F w s j (r l)) M ≤
      ‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F := by
  unfold rootMeshWeight
  rw [discreteVariation_const_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply smoothPolynomialWeight_variation_no_roots F (fun l => Real.exp (r l))
    (Real.exp_monotone.comp hr) M
  intro i x hx hxin
  apply hfree j hj x (hroots i x hx)
  refine ⟨?_, ?_⟩
  · simpa only [hr0] using hxin.1
  · have hlast : Real.exp (r (M - 1)) ≤ Real.exp (s (j + 1)) := by
      rw [← hrM]
      exact Real.exp_le_exp.mpr (hr (Nat.sub_le M 1))
    exact hxin.2.trans_le hlast

theorem rootMeshWeight_bound {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, ‖w x‖ ≤ C)
    (s : ℕ → ℝ) (j : ℕ) (y : ℝ) :
    ‖w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) - rootMeshWeight F w s j y‖ ≤
      2 * C * smoothPolynomialBudget F := by
  calc
    _ ≤ ‖w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)‖ +
        ‖rootMeshWeight F w s j y‖ := norm_sub_le _ _
    _ ≤ C * smoothPolynomialBudget F + C * smoothPolynomialBudget F := by
      simp only [rootMeshWeight, norm_mul]
      exact add_le_add
        (mul_le_mul (hw _) (smoothPolynomialWeight_norm F _) (norm_nonneg _) hC)
        (mul_le_mul (hw _) (smoothPolynomialWeight_norm F _) (norm_nonneg _) hC)
    _ = _ := by ring

theorem rootMeshWeight_eq {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (w : ℝ → ℂ) (S : Finset ℝ)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y)
    (s : ℕ → ℝ) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (j : ℕ) (hj : j < N) (y : ℝ) (hy : y ∈ Set.Ioo (s j) (s (j + 1))) :
    w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) = rootMeshWeight F w s j y := by
  unfold rootMeshWeight
  congr 1
  apply hconst
  apply rootCellCode_eq_of_root_free S (Real.exp (s j)) (Real.exp (s (j + 1)))
    (Real.exp y) (Real.exp ((s j + s (j + 1)) / 2)) (hfree j hj)
  · exact ⟨Real.exp_lt_exp.mpr hy.1, Real.exp_lt_exp.mpr hy.2⟩
  · constructor <;> apply Real.exp_lt_exp.mpr <;> linarith [hy.1, hy.2]

/-- The mesh is supplied before the residue class and coefficient. -/
theorem PublishedProgressionInput.common_root_mesh_prime_comparison (P : PublishedProgressionInput)
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
      ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
        rootMeshWeight F w s j y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N,
        (‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F *
          (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
            Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) +
          2 * C * smoothPolynomialBudget F * Real.exp (-(s j))) := by
  apply P.piecewise_prime_comparison hQ hq hqQ ha s hs N hu hshort
    _ (rootMeshWeight F w s) _ _
  · exact fun j _ => (rootMeshWeight_continuous F w s j).continuousOn
  · exact fun j hj r hr M hr0 hrM => rootMeshWeight_variation F w S hroots s N hfree j hj r hr M hr0 hrM
  · exact fun _ _ => mul_nonneg (mul_nonneg (by positivity) hC) (smoothPolynomialBudget_nonneg F)
  · exact fun j _ y _ => rootMeshWeight_bound F w C hC hw s j y
  · exact fun j hj y hy => rootMeshWeight_eq F w S hconst s N hfree j hj y hy

theorem common_root_mesh_integer_comparison
    (S : Finset ℝ) (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (hfree : ∀ j < N, ∀ r ∈ S, r ∉ Set.Ioo (Real.exp (s j)) (Real.exp (s (j + 1))))
    (q a : ℕ) (hq : 0 < q) (G : ℝ)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (w : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, ‖w x‖ ≤ C)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) :
    ‖complexIntegerInterval q a (s 0) (s N) G
        (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
      ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
        rootMeshWeight F w s j y * (integerLogDensity q G y : ℂ)‖ ≤
      ∑ j ∈ Finset.range N,
        (‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F *
          (2 * Real.exp (-G)) + 2 * C * smoothPolynomialBudget F * Real.exp (-G)) := by
  apply piecewise_integer_comparison q a hq G s hs N
    _ (rootMeshWeight F w s) _ _
  · exact fun j _ => (rootMeshWeight_continuous F w s j).continuousOn
  · exact fun j hj r hr M hr0 hrM => rootMeshWeight_variation F w S hroots s N hfree j hj r hr M hr0 hrM
  · exact fun _ _ => mul_nonneg (mul_nonneg (by positivity) hC) (smoothPolynomialBudget_nonneg F)
  · exact fun j _ y _ => rootMeshWeight_bound F w C hC hw s j y
  · exact fun j hj y hy => rootMeshWeight_eq F w S hconst s N hfree j hj y hy

end Ostmann

end OAI
