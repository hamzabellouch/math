import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevWeights
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

namespace OAI

/-! # Uniform periodization bounds for the localization kernel

Fourteen powers of decay suffice in twelve dimensions. Lattice translation
reduces each continuous frequency to a bounded fundamental cell, and the
already proved lattice p-series controls the remaining sum.
-/

open scoped SchwartzMap

namespace DefocusingNLS

private theorem schwartz_decay_fourteen
    (K : 𝓢(EuclideanSpace ℝ (Fin 12), ℂ)) :
    ∃ M : ℝ, 0 < M ∧ ∀ x, (1 + ‖x‖) ^ 14 * ‖K x‖ ≤ M := by
  let M : ℝ := 2 ^ (14 : ℕ) *
    (Finset.Iic (14, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) K
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (14, 0)) (k := 14) (n := 0) (by decide) (by decide) K x
  have h' : (1 + ‖x‖) ^ 14 * ‖K x‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using h
  exact h'.trans (le_max_left M 1)

private theorem bounded_shift_decay
    (K : EuclideanSpace ℝ (Fin 12) → ℂ) (M : ℝ)
    (hdecay : ∀ x, (1 + ‖x‖) ^ 14 * ‖K x‖ ≤ M)
    (z : EuclideanSpace ℝ (Fin 12)) (hz : ‖z‖ ≤ 12)
    (n : EuclideanSpace ℝ (Fin 12)) :
    ‖K (z - n)‖ ≤ (13 ^ (14 : ℕ) * M) * ((1 + ‖n‖ ^ 2) ^ (7 : ℕ))⁻¹ := by
  have hn : ‖n‖ ≤ ‖z‖ + ‖z - n‖ := by
    calc
      ‖n‖ = ‖z - (z - n)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖z‖ + ‖z - n‖ := norm_sub_le _ _
  have hlin : 1 + ‖n‖ ≤ 13 * (1 + ‖z - n‖) := by
    nlinarith [norm_nonneg (z - n)]
  have hsq : 1 + ‖n‖ ^ 2 ≤ (1 + ‖n‖) ^ 2 := by nlinarith [norm_nonneg n]
  have hpow : (1 + ‖n‖ ^ 2) ^ (7 : ℕ) ≤
      13 ^ (14 : ℕ) * (1 + ‖z - n‖) ^ (14 : ℕ) := by
    calc
      _ ≤ ((1 + ‖n‖) ^ 2) ^ (7 : ℕ) := by gcongr
      _ = (1 + ‖n‖) ^ (14 : ℕ) := by ring
      _ ≤ (13 * (1 + ‖z - n‖)) ^ (14 : ℕ) := by gcongr
      _ = _ := by rw [mul_pow]
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + ‖n‖ ^ 2) ^ (7 : ℕ))).2
  calc
    _ = (1 + ‖n‖ ^ 2) ^ (7 : ℕ) * ‖K (z - n)‖ := mul_comm _ _
    _ ≤ (13 ^ (14 : ℕ) * (1 + ‖z - n‖) ^ (14 : ℕ)) * ‖K (z - n)‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = 13 ^ (14 : ℕ) * ((1 + ‖z - n‖) ^ (14 : ℕ) * ‖K (z - n)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hdecay (z - n)) (by positivity)

private theorem summable_localization_majorant :
    Summable (fun n : frequencyLattice => ((1 + ‖n‖ ^ 2) ^ (7 : ℕ))⁻¹) := by
  have h := summable_sobolev_variances 0 7 (by norm_num)
  convert h using 1
  ext n
  norm_num [Real.rpow_neg]

/-- Every Schwartz localization kernel has a uniform lattice-periodization bound. -/
theorem exists_schwartz_periodization_bound (K : 𝓢(EuclideanSpace ℝ (Fin 12), ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset frequencyLattice) (x : EuclideanSpace ℝ (Fin 12)),
      ∑ n ∈ S, ‖K (x - n)‖ ≤ C := by
  classical
  obtain ⟨M, hM, hdecay⟩ := schwartz_decay_fourteen K
  let D : ℝ := 13 ^ (14 : ℕ) * M
  let seq := fun n : frequencyLattice => ((1 + ‖n‖ ^ 2) ^ (7 : ℕ))⁻¹
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hseq : Summable seq := summable_localization_majorant
  refine ⟨D * ∑' n, seq n, mul_nonneg hD (tsum_nonneg (fun _ => by dsimp [seq]; positivity)), ?_⟩
  intro S x
  let b := (EuclideanSpace.basisFun (Fin 12) ℝ).toBasis
  let l : frequencyLattice := ZSpan.floor b x
  let z := ZSpan.fract b x
  have hz : ‖z‖ ≤ 12 := by
    have h := ZSpan.norm_fract_le b x
    simpa [b, OrthonormalBasis.norm_eq_one] using h
  have hx (n : frequencyLattice) : x - (n : EuclideanSpace ℝ (Fin 12)) =
      z - ((n - l : frequencyLattice) : EuclideanSpace ℝ (Fin 12)) := by
    dsimp [z, ZSpan.fract]
    change x - (n : EuclideanSpace ℝ (Fin 12)) = (x - (l : EuclideanSpace ℝ (Fin 12))) -
      ((n : EuclideanSpace ℝ (Fin 12)) - (l : EuclideanSpace ℝ (Fin 12)))
    abel
  have hs : Summable (fun n => seq (n - l)) := (Equiv.subRight l).summable_iff.mpr hseq
  calc
    _ ≤ D * ∑ n ∈ S, seq (n - l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n _
      rw [hx]
      exact bounded_shift_decay K M hdecay z hz (n - l)
    _ ≤ D * ∑' n, seq (n - l) := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum S (fun _ _ => by dsimp [seq]; positivity)) hD
    _ = _ := by
      congr 1
      exact (Equiv.subRight l).tsum_eq seq

end DefocusingNLS

end OAI
