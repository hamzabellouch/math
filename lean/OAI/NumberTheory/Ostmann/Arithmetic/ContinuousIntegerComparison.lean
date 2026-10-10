import OAI.NumberTheory.Ostmann.Arithmetic.IntegerIntervalVariation
import OAI.NumberTheory.Ostmann.Arithmetic.ContinuousIntervalMesh

namespace OAI

/-! # Continuous weights under the original external integer law -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem complex_integer_density_freeze (q : ℕ) (hq : 0 < q) (u v G : ℝ) (huv : u ≤ v)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc u v)) (c : ℂ) (η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ y ∈ Set.Ioc u v, ‖w y - c‖ ≤ η) :
    ‖(∫ y in Set.Ioc u v, w y * (integerLogDensity q G y : ℂ)) -
      c * (∫ y in Set.Ioc u v, integerLogDensity q G y : ℝ)‖ ≤
        η * Real.exp (v - G) * (v - u) := by
  have hc := (continuous_integerLogDensity q G).continuousOn (s := Set.Icc u v)
  have hiw : IntegrableOn (fun y => w y * (integerLogDensity q G y : ℂ)) (Set.Ioc u v) :=
    (hwc.mul (Complex.continuous_ofReal.comp_continuousOn hc)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hic : IntegrableOn (fun y => c * (integerLogDensity q G y : ℂ)) (Set.Ioc u v) :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hc)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have heq : (∫ y in Set.Ioc u v, w y * (integerLogDensity q G y : ℂ)) -
      c * (∫ y in Set.Ioc u v, integerLogDensity q G y : ℝ) =
      ∫ y in Set.Ioc u v, (w y - c) * (integerLogDensity q G y : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_const_mul, ← integral_sub hiw hic]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y _
    ring
  rw [heq]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (C := η * Real.exp (v - G))
    (f := fun y => (w y - c) * (integerLogDensity q G y : ℂ))
    (fun y hy => by
      have hy' := (Set.uIoc_of_le huv) ▸ hy
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hw y hy') (integerLogDensity_abs_le q hq G hy'.2) (abs_nonneg _) hη)
  rwa [intervalIntegral.integral_of_le huv, abs_of_nonneg (sub_nonneg.mpr huv)] at hi

/-- A partition only incurs oscillation times total mass and interval length.
Its progression error is bounded by variation independently of the mesh. -/
theorem integer_partition_variation (q a : ℕ) (hq : 0 < q) (G : ℝ)
    (s : ℕ → ℝ) (hs : Monotone s) (N : ℕ)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc (s 0) (s N))) (η : ℝ) (hη : 0 ≤ η)
    (hw : ∀ j < N, ∀ y ∈ Set.Ioc (s j) (s (j + 1)), ‖w y - w (s j)‖ ≤ η) :
    ‖complexIntegerInterval q a (s 0) (s N) G w -
        ∫ y in Set.Ioc (s 0) (s N), w y * (integerLogDensity q G y : ℂ)‖ ≤
      discreteVariation (fun j => w (s j)) N * (2 * Real.exp (-G)) +
      η * (integerLogCellMass q a (s 0) (s N) G + Real.exp (s N - G) * (s N - s 0)) := by
  let A (j : ℕ) := complexIntegerInterval q a (s j) (s (j + 1)) G w
  let B (j : ℕ) := w (s j) * (integerLogCellMass q a (s j) (s (j + 1)) G : ℂ)
  let C (j : ℕ) := w (s j) * (∫ y in Set.Ioc (s j) (s (j + 1)), integerLogDensity q G y : ℝ)
  let D (j : ℕ) := ∫ y in Set.Ioc (s j) (s (j + 1)), w y * (integerLogDensity q G y : ℂ)
  have hA : ‖∑ j ∈ Finset.range N, (A j - B j)‖ ≤
      η * integerLogCellMass q a (s 0) (s N) G := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.range N, η * integerLogCellMass q a (s j) (s (j + 1)) G := by
        apply Finset.sum_le_sum
        intro j hj
        exact complexIntegerInterval_freeze q a _ _ G w _ η (hw j (Finset.mem_range.mp hj))
      _ = _ := by rw [← Finset.mul_sum, integerLogCellMass_partition q a G s hs N]
  have hD : ‖∑ j ∈ Finset.range N, (C j - D j)‖ ≤
      η * Real.exp (s N - G) * (s N - s 0) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.range N, η * Real.exp (s N - G) * (s (j + 1) - s j) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_sub_rev]
        apply (complex_integer_density_freeze q hq _ _ G (hs (Nat.le_succ _)) w
          (hwc.mono (by
            intro y hy
            exact ⟨(hs (Nat.zero_le _)).trans hy.1,
              hy.2.trans (hs (by have := Finset.mem_range.mp hj; omega))⟩))
          _ η hη (hw j (Finset.mem_range.mp hj))).trans
        apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr (hs (Nat.le_succ _)))
        apply mul_le_mul_of_nonneg_left _ hη
        apply Real.exp_le_exp.mpr
        exact sub_le_sub_right (hs (by have := Finset.mem_range.mp hj; omega)) G
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub s]
  have hBC : ‖∑ j ∈ Finset.range N, (B j - C j)‖ ≤
      discreteVariation (fun j => w (s j)) N * (2 * Real.exp (-G)) := by
    simpa only [B, C, ← mul_sub, ← Complex.ofReal_sub] using
      weighted_integer_interval_variation q a hq G s hs N (fun j => w (s j))
  have hid : complexIntegerInterval q a (s 0) (s N) G w -
        (∫ y in Set.Ioc (s 0) (s N), w y * (integerLogDensity q G y : ℂ)) =
      (∑ j ∈ Finset.range N, (A j - B j)) +
        (∑ j ∈ Finset.range N, (B j - C j)) + (∑ j ∈ Finset.range N, (C j - D j)) := by
    have hcont : ContinuousOn (fun y => w y * (integerLogDensity q G y : ℂ))
        (Set.Icc (s 0) (s N)) :=
      hwc.mul (Complex.continuous_ofReal.comp_continuousOn (continuous_integerLogDensity q G).continuousOn)
    rw [← complexIntegerInterval_partition q a G s hs w N,
      ← integral_Ioc_partition s hs N (fun y => w y * (integerLogDensity q G y : ℂ)) hcont]
    simp only [Finset.sum_sub_distrib, A, D]
    ring
  rw [hid]
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    (by linarith [add_le_add (add_le_add hA hBC) hD])

/-- The external integer comparison keeps the original normalization and
requires no fixed mesh or partition-count loss. -/
theorem continuous_integer_comparison (q a : ℕ) (hq : 0 < q) (u v G : ℝ) (huv : u ≤ v)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc u v)) (V : ℝ)
    (hV : ∀ (s : ℕ → ℝ), Monotone s → ∀ N, s 0 = u → s N = v →
      discreteVariation (fun j => w (s j)) N ≤ V) :
    ‖complexIntegerInterval q a u v G w -
        ∫ y in Set.Ioc u v, w y * (integerLogDensity q G y : ℂ)‖ ≤
      V * (2 * Real.exp (-G)) := by
  let M := integerLogCellMass q a u v G + Real.exp (v - G) * (v - u)
  have hM : 0 ≤ M := add_nonneg (integerLogCellMass_nonneg q a u v G)
    (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr huv))
  have hM1 : 0 < M + 1 := by linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  let η := ε / (M + 1)
  have hη : 0 < η := div_pos hε hM1
  obtain ⟨s, N, _hN, hs, hs0, hsN, hosc⟩ := continuous_interval_mesh u v huv w hwc η hη
  have hc : ContinuousOn w (Set.Icc (s 0) (s N)) := by simpa only [hs0, hsN] using hwc
  have hb := integer_partition_variation q a hq G s hs N w hc η hη.le hosc
  rw [hs0, hsN] at hb
  apply hb.trans
  have hvar := mul_le_mul_of_nonneg_right (hV s hs N hs0 hsN) (by positivity : 0 ≤ 2 * Real.exp (-G))
  have hsmall : η * M ≤ ε := by
    have hid : η * (M + 1) = ε := by dsimp [η]; field_simp
    nlinarith
  exact add_le_add hvar hsmall

end Ostmann

end OAI
