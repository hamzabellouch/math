import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ScaledLatticeKernel
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzLocalizationKernel

namespace OAI

/-! # Uniform sampling of Schwartz Fourier kernels

The normalized sampling sum has a bound independent of the expanding
period.  The same statement holds with either Sobolev weight.
-/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem schwartz_sampling_decay (K : 𝓢(E, ℂ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : E,
      ‖K x‖ ^ 2 ≤ D ^ 2 * ((1 + ‖x‖ ^ 2) ^ (12 : ℕ))⁻¹ := by
  let M : ℝ := 2 ^ (12 : ℕ) *
    (Finset.Iic (12, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) K
  let D := max M 1
  have hD : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  refine ⟨D, hD, ?_⟩
  intro x
  have hbase := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (12, 0)) (k := 12) (n := 0) (by decide) (by decide) K x
  have hb : (1 + ‖x‖) ^ 12 * ‖K x‖ ≤ D := by
    have h : (1 + ‖x‖) ^ 12 * ‖K x‖ ≤ M := by
      simpa only [norm_iteratedFDeriv_zero] using hbase
    exact h.trans (le_max_left _ _)
  have hw : (1 + ‖x‖ ^ 2) ^ 6 ≤ (1 + ‖x‖) ^ 12 := by
    calc
      _ ≤ ((1 + ‖x‖) ^ 2) ^ 6 :=
        pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg x]) _
      _ = _ := by ring
  have he := (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans hb
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + ‖x‖ ^ 2) ^ 6 * ‖K x‖) he 2
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + ‖x‖ ^ 2) ^ (12 : ℕ))).mpr
  nlinarith [show ((1 + ‖x‖ ^ 2) ^ 6 * ‖K x‖) ^ 2 =
    ‖K x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (12 : ℕ) by ring]

theorem exists_schwartz_scaledLattice_l2_bound (K : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      Summable (fun n : frequencyLattice => ‖K ((L⁻¹ : ℝ) • (n : E))‖ ^ 2) ∧
        (∑' n : frequencyLattice, ‖K ((L⁻¹ : ℝ) • (n : E))‖ ^ 2) ≤ C * L ^ (12 : ℕ) := by
  obtain ⟨D, _hD, hb⟩ := schwartz_sampling_decay K
  refine ⟨D ^ 2 * (1 + 2 * Real.pi) ^ (12 : ℕ), by positivity, ?_⟩
  intro L hL
  obtain ⟨hs, hsum⟩ := scaledRadialKernel_sum L hL
  have hmajor := hs.mul_left (D ^ 2)
  have hS : Summable (fun n : frequencyLattice => ‖K ((L⁻¹ : ℝ) • (n : E))‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => hb _) hmajor
  refine ⟨hS, ?_⟩
  calc
    _ ≤ ∑' n : frequencyLattice,
        D ^ 2 * ((1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ (12 : ℕ))⁻¹ :=
      hS.tsum_le_tsum (fun n => hb _) hmajor
    _ = D ^ 2 * ∑' n : frequencyLattice,
        ((1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ (12 : ℕ))⁻¹ := tsum_mul_left
    _ ≤ D ^ 2 * (((1 + 2 * Real.pi) * L) ^ (12 : ℕ)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg D)
    _ = _ := by rw [mul_pow]; ring

theorem exists_weightedSchwartz_scaledLattice_l2_bound (s : ℝ) (K : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      Summable (fun n : frequencyLattice =>
        (1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ s * ‖K ((L⁻¹ : ℝ) • (n : E))‖ ^ 2) ∧
        (∑' n : frequencyLattice,
          (1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ s * ‖K ((L⁻¹ : ℝ) • (n : E))‖ ^ 2) ≤
          C * L ^ (12 : ℕ) := by
  have he (x : E) : ‖weightedSchwartzKernel s K x‖ ^ 2 =
      (1 + ‖x‖ ^ 2) ^ s * ‖K x‖ ^ 2 := by
    rw [weightedSchwartzKernel_norm, mul_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    congr 2
    ring
  simpa only [he] using exists_schwartz_scaledLattice_l2_bound (weightedSchwartzKernel s K)

end DefocusingNLS

end OAI
