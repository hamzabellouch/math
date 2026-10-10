import OAI.Combinatorics.ContingencyTables.Dense.DenseReindexedVolume
import OAI.Combinatorics.ContingencyTables.Dense.DenseLayerArithmetic
import OAI.Combinatorics.ContingencyTables.Dense.GridPartition

namespace OAI

/-! # Normalizer bound for the actual dense bin weights -/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

/-- The finite layer estimate gives the stronger constant 16 in place of
the manuscript's 32. No interpolation or Cheeger input is needed here. -/
theorem denseBin_normalizer_bound (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) :
    ENNReal.ofReal (∑ a : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e a) ≤
      16 * volume {x | denseGridFeasible R P d e x} := by
  let K := 4 * d ^ 8
  let A := (d : ℝ) ^ 4
  let p := denseGridPenalty R P d e
  let ρ := DenseWeights.density A p
  let V := volume {x | denseGridFeasible R P d e x}
  let N := 4 * d ^ 5
  let t (j : ℕ) := (2 : ℝ) ^ (-(j : ℝ)) *
    Real.exp (2 * (d : ℝ) ^ 2 * ((d : ℝ) / (d : ℝ) ^ 8 + ((j : ℝ) + 1) / (d : ℝ) ^ 4))
  have hp : Continuous p := denseGridPenalty_continuous R P d e
  have hρ : Continuous ρ := DenseWeights.density_continuous A p hp
  have hi : IntegrableOn ρ (ambientBox q K) := hρ.integrableOn_Icc
  have hc : MeasurableSet {x : Fin q → ℝ | Cube K x} := (cube_finiteBox (q := q) (K := K)).isOpen.measurableSet
  have hsub : {x : Fin q → ℝ | Cube K x} ⊆ ambientBox q K :=
    fun x hx => ⟨fun j => (hx j).1.le, fun j => (hx j).2.le⟩
  have hbin (a : Grid (I := Fin q) K) : denseBinWeight R P d e a / 4 ≤ ∫ x in binSet a, ρ x := by
    have hb := setIntegral_ge_of_const_le_real (binSet_measurable a)
      (show volume (binSet a) ≠ ⊤ by rw [binSet_volume]; simp)
      (fun x hx => (denseGrid_bin_comparison R P d hd hR hP hRmax hPmax hfree e a x
        (fun j => ⟨(hx j).1.le, (hx j).2.le⟩)).1)
      (hi.mono_set (binSet_subset_ambient a))
    simpa only [Measure.real, binSet_volume, ENNReal.toReal_one, mul_one, denseBinWeight] using hb
  have hmass : (∑ a : Grid (I := Fin q) K, denseBinWeight R P d e a) ≤
      4 * ∫ x in {x | Cube K x}, ρ x := by
    have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hbin a)
    rw [← Finset.sum_div, ← cube_integral_bins ρ hi] at hs
    linarith
  have hZ : ENNReal.ofReal (∑ a : Grid (I := Fin q) K, denseBinWeight R P d e a) ≤
      4 * ∫⁻ x in {x | Cube K x}, ENNReal.ofReal (ρ x) := by
    have h := ENNReal.ofReal_le_ofReal hmass
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ofReal_integral_eq_lintegral_ofReal (hi.mono_set hsub)
        (Filter.Eventually.of_forall (fun x => (DenseWeights.density_pos A p x).le))] at h
    simpa only [ENNReal.ofReal_ofNat] using h
  have hbound (x : Fin q → ℝ) (hx : Cube K x) : 0 ≤ A * p x ∧ A * p x ≤ N := by
    have hcube (z : I × J) : 0 ≤ x (e z) ∧ x (e z) ≤ 4 * (d : ℝ) ^ 8 := by
      refine ⟨(hx (e z)).1.le, ?_⟩
      simpa only [K, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using (hx (e z)).2.le
    have hpen := DenseAffine.densePenalty_cube_bound R P d hd hR hP hRmax hPmax
      hdimR hdimP hfree htotal _ hcube
    have hm := mul_le_mul_of_nonneg_left hpen.2 (show (0 : ℝ) ≤ A by positivity)
    constructor
    · exact mul_nonneg (by positivity) hpen.1
    · change (d : ℝ) ^ 4 * p x ≤ (4 * d ^ 5 : ℕ)
      change (d : ℝ) ^ 4 * p x ≤ (d : ℝ) ^ 4 * (4 * d) at hm
      push_cast
      nlinarith [show (d : ℝ) ^ 4 * (4 * d) = 4 * (d : ℝ) ^ 5 by ring]
  have hL := DenseWeights.density_lintegral_le_layers volume A p hp.measurable
    {x | Cube K x} hc N hbound
  have hL' : (∫⁻ x in {x | Cube K x}, ENNReal.ofReal (ρ x)) ≤
      ENNReal.ofReal (∑ j ∈ Finset.range (N + 1), t j) * V := by
    apply hL.trans
    calc
      _ ≤ ∑ j ∈ Finset.range (N + 1),
          ENNReal.ofReal ((2 : ℝ) ^ (-(j : ℝ))) *
            (ENNReal.ofReal (Real.exp (2 * (d : ℝ) ^ 2 *
              ((d : ℝ) / (d : ℝ) ^ 8 + ((j : ℝ) + 1) / (d : ℝ) ^ 4))) * V) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_right
        exact (measure_mono Set.inter_subset_right).trans
          (denseGrid_layer_volume R P d hd hR hP hdimR hdimP hfree htotal e j)
      _ = (∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (t j)) * V := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-(j : ℝ)))]
      _ = _ := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => show 0 ≤ t j by positivity)]
  calc
    _ ≤ 4 * ∫⁻ x in {x | Cube K x}, ENNReal.ofReal (ρ x) := hZ
    _ ≤ 4 * (ENNReal.ofReal (∑ j ∈ Finset.range (N + 1), t j) * V) := mul_le_mul_right hL' 4
    _ = ENNReal.ofReal (4 * (∑ j ∈ Finset.range (N + 1), t j)) * V := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat, mul_assoc]
    _ ≤ 16 * V := by
      apply mul_le_mul_left
      have h := ENNReal.ofReal_le_ofReal (DenseAffine.dense_layer_sum d hd (N + 1))
      simpa only [ENNReal.ofReal_ofNat] using h

end

end ContingencyTables.GridBoundary

end OAI
