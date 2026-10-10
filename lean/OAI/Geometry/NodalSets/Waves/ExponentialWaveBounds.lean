import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import OAI.Geometry.NodalSets.Waves.SmoothWaveOperator

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma norm_iteratedFDeriv_complex_exp (k : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ k Complex.exp z‖ = Real.exp z.re := by
  have he := (Complex.contDiff_exp (𝕜 := ℂ) (n := k)).contDiffAt.restrictScalars_iteratedFDeriv
    (𝕜 := ℝ) (x := z)
  rw [← he]
  simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hd : iteratedDeriv k Complex.exp z = Complex.exp z := by
    simpa using congrFun (iteratedDeriv_cexp_const_mul k 1) z
  rw [hd, Complex.norm_exp]

theorem waveExp_derivative_bound {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi)
    (k : ℕ) (x : Coord) {D N : ℝ} (hD : 1 ≤ D) (hN : 1 ≤ N)
    (hphi : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i phi x‖ ≤ D) :
    ‖iteratedFDeriv ℝ k (waveExp phi N) x‖ ≤
      (k.factorial : ℝ) * D ^ k * N ^ k * Real.exp (N * (phi x).re) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hDN : 1 ≤ D * N := one_le_mul_of_one_le_of_one_le hD hN
  have hb : ∀ i, 1 ≤ i → i ≤ k →
      ‖iteratedFDeriv ℝ i (fun z ↦ (N : ℂ) * phi z) x‖ ≤ (D * N) ^ i := by
    intro i hi hik
    change ‖iteratedFDeriv ℝ i (fun z ↦ (N : ℂ) • phi z) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hp.of_le (by
      exact_mod_cast (show (i : ℕ∞) ≤ ⊤ from le_top))).contDiffAt, norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNp]
    calc
      _ ≤ N * D := mul_le_mul_of_nonneg_left (hphi i hi hik) hNp.le
      _ = (D * N) ^ 1 := by ring
      _ ≤ _ := pow_le_pow_right₀ hDN hi
  have he := norm_iteratedFDeriv_comp_le
    (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)) (contDiff_const.mul hp) (n := k)
    (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)) x
    (fun i _ ↦ le_of_eq (norm_iteratedFDeriv_complex_exp i ((N : ℂ) * phi x))) hb
  change ‖iteratedFDeriv ℝ k (fun z ↦ Complex.exp ((N : ℂ) * phi z)) x‖ ≤ _
  simpa [Function.comp_def, mul_pow, mul_assoc, mul_left_comm, mul_comm] using he

theorem waveExp_gaussian_derivative_bound {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi)
    (k : ℕ) (x : Coord) {D N S c r : ℝ} (hD : 1 ≤ D) (hN : 1 ≤ N)
    (hphi : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i phi x‖ ≤ D)
    (hgap : (phi x).re - S ≤ -c * r ^ 2) :
    ‖iteratedFDeriv ℝ k (waveExp phi N) x‖ ≤
      (k.factorial : ℝ) * D ^ k * N ^ k * Real.exp (N * S - c * N * r ^ 2) := by
  apply (waveExp_derivative_bound hp k x hD hN hphi).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hgap (le_trans zero_le_one hN)
  nlinarith

end
end Yau.Jets

end OAI
