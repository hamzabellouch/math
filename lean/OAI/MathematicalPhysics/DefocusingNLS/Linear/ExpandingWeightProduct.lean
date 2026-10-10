import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOneDimensional
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-! # A separable majorant for the expanding-torus inverse weight -/

open Set

namespace DefocusingNLS

theorem expandingOneDimWeight_coordinate_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (n : frequencyLattice) (j : Fin 12) :
    expandingOneDimWeight a k L (frequencyCoordinates n j) ≤
      L ^ (a / 6) * (1 + ‖n‖ ^ 2) ^ ((6 - a) / 12) +
        L ^ (1 - k / 6) * ‖n‖ ^ (k / 6) := by
  have hs := frequencyCoordinates_sq_le n j
  have hn : |(frequencyCoordinates n j : ℝ)| ≤ ‖n‖ := by
    nlinarith [sq_abs (frequencyCoordinates n j : ℝ), norm_nonneg n,
      abs_nonneg (frequencyCoordinates n j : ℝ)]
  unfold expandingOneDimWeight
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (add_le_add le_rfl hs) (by linarith))
      (by positivity)
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hn (by linarith)) (by positivity)

theorem expandingWeight_product_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (n : frequencyLattice) :
    (∏ j : Fin 12, expandingOneDimWeight a k L (frequencyCoordinates n j)) ≤
      2 ^ 12 * expandingSobolevWeightSq a k L n := by
  let A := L ^ (a / 6) * (1 + ‖n‖ ^ 2) ^ ((6 - a) / 12)
  let B := L ^ (1 - k / 6) * ‖n‖ ^ (k / 6)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hAp : A ^ 12 = L ^ (2 * a) * (1 + ‖n‖ ^ 2) ^ (6 - a) := by
    dsimp [A]
    rw [mul_pow]
    congr 1
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ L)]
      congr 1
      ring
    · have he : ((6 - a) / 12) * (12 : ℝ) = 6 - a := by ring
      rw [← Real.rpow_natCast]
      have hh := (Real.rpow_mul (x := 1 + ‖n‖ ^ 2) (by positivity) ((6 - a) / 12) 12).symm
      rw [he] at hh
      exact hh
  have hBp : B ^ 12 = L ^ (12 - 2 * k) * ‖n‖ ^ (2 * k) := by
    dsimp [B]
    rw [mul_pow]
    congr 1
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ L)]
      congr 1
      ring
    · have he : (k / 6) * (12 : ℝ) = 2 * k := by ring
      rw [← Real.rpow_natCast]
      have hh := (Real.rpow_mul (x := ‖n‖) (norm_nonneg n) (k / 6) 12).symm
      rw [he] at hh
      exact hh
  have hpow : (A + B) ^ 12 ≤ (2 : ℝ) ^ 12 * (A ^ 12 + B ^ 12) := by
    rcases le_total A B with h | h
    · calc
        _ ≤ (2 * B) ^ 12 := by gcongr; linarith
        _ = (2 : ℝ) ^ 12 * B ^ 12 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (pow_nonneg hA 12)) (by positivity)
    · calc
        _ ≤ (2 * A) ^ 12 := by gcongr; linarith
        _ = (2 : ℝ) ^ 12 * A ^ 12 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (pow_nonneg hB 12)) (by positivity)
  calc
    _ ≤ ∏ _ : Fin 12, (A + B) := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact (expandingOneDimWeight_pos a k L _ hL).le
      · intro j _
        exact expandingOneDimWeight_coordinate_le a k L ha ha1 hk hL n j
    _ = (A + B) ^ 12 := by simp
    _ ≤ (2 : ℝ) ^ 12 * (A ^ 12 + B ^ 12) := hpow
    _ = _ := by rw [hAp, hBp]; rfl

/-- The inverse radial weight is dominated by a product with a uniform integer sum. -/
theorem expandingSobolevWeight_inv_le_product (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (n : frequencyLattice) :
    (expandingSobolevWeightSq a k L n)⁻¹ ≤
      2 ^ 12 * ∏ j : Fin 12, expandingOneDimKernel a k L (frequencyCoordinates n j) := by
  have hp : 0 < ∏ j : Fin 12, expandingOneDimWeight a k L (frequencyCoordinates n j) :=
    Finset.prod_pos (fun j _ => expandingOneDimWeight_pos a k L _ hL)
  have h := (div_le_div_iff₀ (expandingSobolevWeightSq_pos a k L hL n) hp).mpr
    (show (1 : ℝ) * (∏ j : Fin 12, expandingOneDimWeight a k L (frequencyCoordinates n j)) ≤
      2 ^ 12 * expandingSobolevWeightSq a k L n by
      simpa only [one_mul] using expandingWeight_product_le a k L ha ha1 hk hL n)
  simpa only [one_div, one_mul, div_eq_mul_inv, Finset.prod_inv_distrib, expandingOneDimKernel] using h

private theorem frequencyCoordinates_injective : Function.Injective frequencyCoordinates := by
  intro n m h
  apply Subtype.ext
  ext j
  have hc := congrFun h j
  exact_mod_cast (frequencyCoordinates_coe n j).symm.trans
    ((congrArg (fun z : ℤ => (z : ℝ)) hc).trans (frequencyCoordinates_coe m j))

/-- Summing the separable majorant uses only finite products and the one-dimensional sum. -/
theorem sum_expandingKernel_product_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (S : Finset frequencyLattice) :
    (∑ n ∈ S, ∏ j : Fin 12, expandingOneDimKernel a k L (frequencyCoordinates n j)) ≤
      (1 + 2 * (1 / (a / 6) + 1 / (k / 6 - 1))) ^ 12 := by
  classical
  let K : ℤ → ℝ := fun z => expandingOneDimKernel a k L z
  let U : Finset ℤ := S.biUnion (fun n => Finset.univ.image (frequencyCoordinates n))
  let T : Finset (Fin 12 → ℤ) := S.image frequencyCoordinates
  have hTU : T ⊆ Fintype.piFinset (fun _ : Fin 12 => U) := by
    intro p hp
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
    simp only [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_biUnion.mpr ⟨n, hn, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨hKs, hKb⟩ := expandingOneDimKernel_integer_sum_bound a k L ha ha1 hk hL
  have hU : (∑ z ∈ U, K z) ≤ 1 + 2 * (1 / (a / 6) + 1 / (k / 6 - 1)) :=
    (hKs.sum_le_tsum U (fun z _ => expandingOneDimKernel_nonneg a k L z hL)).trans hKb
  have hUnonneg : 0 ≤ ∑ z ∈ U, K z :=
    Finset.sum_nonneg (fun z _ => expandingOneDimKernel_nonneg a k L z hL)
  calc
    _ = ∑ p ∈ T, ∏ j : Fin 12, K (p j) := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => frequencyCoordinates_injective h
    _ ≤ ∑ p ∈ Fintype.piFinset (fun _ : Fin 12 => U), ∏ j : Fin 12, K (p j) :=
      Finset.sum_le_sum_of_subset_of_nonneg hTU (fun _ _ _ => by
        apply Finset.prod_nonneg
        intro j _
        exact expandingOneDimKernel_nonneg a k L _ hL)
    _ = (∑ z ∈ U, K z) ^ 12 := by
      rw [Finset.sum_prod_piFinset]
      simp
    _ ≤ _ := by gcongr

/-- The exact normalized inverse weights have a scale-independent summability bound. -/
theorem summable_expandingSobolevWeight_inv (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) :
    Summable (fun n : frequencyLattice => (expandingSobolevWeightSq a k L n)⁻¹) ∧
      (∑' n : frequencyLattice, (expandingSobolevWeightSq a k L n)⁻¹) ≤
        2 ^ 12 * (1 + 2 * (1 / (a / 6) + 1 / (k / 6 - 1))) ^ 12 := by
  have hnon : ∀ n : frequencyLattice, 0 ≤ (expandingSobolevWeightSq a k L n)⁻¹ :=
    fun n => (inv_pos.mpr (expandingSobolevWeightSq_pos a k L hL n)).le
  have hb (S : Finset frequencyLattice) :
      (∑ n ∈ S, (expandingSobolevWeightSq a k L n)⁻¹) ≤
        2 ^ 12 * (1 + 2 * (1 / (a / 6) + 1 / (k / 6 - 1))) ^ 12 := by
    calc
      _ ≤ ∑ n ∈ S, 2 ^ 12 * ∏ j : Fin 12,
          expandingOneDimKernel a k L (frequencyCoordinates n j) :=
        Finset.sum_le_sum (fun n _ => expandingSobolevWeight_inv_le_product a k L ha ha1 hk hL n)
      _ = 2 ^ 12 * (∑ n ∈ S, ∏ j : Fin 12,
          expandingOneDimKernel a k L (frequencyCoordinates n j)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_expandingKernel_product_le a k L ha ha1 hk hL S)
        (by positivity)
  have hs := summable_of_sum_le hnon hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

end DefocusingNLS

end OAI
