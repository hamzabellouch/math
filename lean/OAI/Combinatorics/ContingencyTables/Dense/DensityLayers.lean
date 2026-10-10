import OAI.Combinatorics.ContingencyTables.Dense.DenseWeights
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace OAI

/-!
# A finite penalty-layer bound

The actual dense cube has bounded exponent, so a finite layer sum suffices
for its normalizer. This avoids any infinite layer decomposition.
-/

namespace ContingencyTables.DenseWeights

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

def layerSet {X : Type*} (A : ℝ) (p : X → ℝ) (j : ℕ) : Set X :=
  {x | A * p x ≤ (j : ℝ) + 1}

theorem density_le_finite_layers {X : Type*} (A : ℝ) (p : X → ℝ) (N : ℕ)
    (x : X) (hx₀ : 0 ≤ A * p x) (hxN : A * p x ≤ N) :
    ENNReal.ofReal (density A p x) ≤
      ∑ j ∈ Finset.range (N + 1),
        (layerSet A p j).indicator (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ)))) x := by
  let j := (⌊A * p x⌋ : ℤ).toNat
  have hf : (0 : ℤ) ≤ ⌊A * p x⌋ := Int.floor_nonneg.mpr hx₀
  have hjcast : (j : ℝ) = (⌊A * p x⌋ : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg hf
  have hj : j ∈ Finset.range (N + 1) := by
    apply Finset.mem_range.mpr
    have hb : (j : ℝ) ≤ N := by
      rw [hjcast]
      exact (Int.floor_le _).trans hxN
    have hn : j ≤ N := by exact_mod_cast hb
    omega
  have hxj : x ∈ layerSet A p j := by
    change A * p x ≤ (j : ℝ) + 1
    rw [hjcast]
    exact (Int.lt_floor_add_one _).le
  have hweight : density A p x ≤ (2 : ℝ) ^ (-(j : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [hjcast]
    linarith [Int.floor_le (A * p x)]
  calc
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ))) := ENNReal.ofReal_le_ofReal hweight
    _ = (layerSet A p j).indicator (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ)))) x := by
      rw [Set.indicator_of_mem hxj]
    _ ≤ _ := Finset.single_le_sum
      (f := fun k : ℕ => (layerSet A p k).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ)))) x) (fun _ _ => bot_le) hj

theorem density_lintegral_le_layers {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : ℝ) (p : X → ℝ) (hp : Measurable p)
    (K : Set X) (hK : MeasurableSet K) (N : ℕ)
    (hbound : ∀ x ∈ K, 0 ≤ A * p x ∧ A * p x ≤ N) :
    (∫⁻ x in K, ENNReal.ofReal (density A p x) ∂μ) ≤
      ∑ j ∈ Finset.range (N + 1),
        ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ))) * μ (K ∩ layerSet A p j) := by
  have hmeas (j : ℕ) : MeasurableSet (layerSet A p j) :=
    measurableSet_le (measurable_const.mul hp) measurable_const
  calc
    _ ≤ ∫⁻ x in K, ∑ j ∈ Finset.range (N + 1),
        (layerSet A p j).indicator (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ)))) x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK] with x hx
      exact density_le_finite_layers A p N x (hbound x hx).1 (hbound x hx).2
    _ = _ := by
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [lintegral_indicator (hmeas j), lintegral_const, Measure.restrict_restrict (hmeas j),
          Measure.restrict_apply_univ, Set.inter_comm]
      · intro j _
        exact (measurable_const : Measurable (fun _ : X =>
          ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ))))).indicator (hmeas j)

end

end ContingencyTables.DenseWeights

end OAI
