import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProductCommutatorBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzTorusSampling

namespace OAI

/-! # Uniform commutator moments of sampled Schwartz coefficients -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem schwartzCommutator_decay (N : ℕ) (K : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E,
      ‖x‖ * (2 + ‖x‖) ^ N * ‖K x‖ ≤ C * ((1 + ‖x‖ ^ 2) ^ (12 : ℕ))⁻¹ := by
  let M : ℝ := 2 ^ (N + 25) *
    (Finset.Iic (N + 25, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) K
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  refine ⟨2 ^ N * M, by positivity, ?_⟩
  intro x
  have hbase : (1 + ‖x‖) ^ (N + 25) * ‖K x‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
        (m := (N + 25, 0)) (k := N + 25) (n := 0) (by rfl) (by rfl) K x
  have hp : ‖x‖ * (2 + ‖x‖) ^ N ≤ 2 ^ N * (1 + ‖x‖) ^ (N + 1) := by
    calc
      _ ≤ (1 + ‖x‖) * (2 * (1 + ‖x‖)) ^ N := by gcongr <;> linarith [norm_nonneg x]
      _ = _ := by rw [mul_pow, pow_succ]; ring
  have hd : (1 + ‖x‖ ^ 2) ^ 12 ≤ (1 + ‖x‖) ^ 24 := by
    calc
      _ ≤ ((1 + ‖x‖) ^ 2) ^ 12 :=
        pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg x]) 12
      _ = _ := by rw [← pow_mul]
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + ‖x‖ ^ 2) ^ (12 : ℕ))).mpr
  calc
    _ ≤ (2 ^ N * (1 + ‖x‖) ^ (N + 1)) * ‖K x‖ * (1 + ‖x‖) ^ 24 := by gcongr
    _ = 2 ^ N * ((1 + ‖x‖) ^ (N + 25) * ‖K x‖) := by
      rw [show N + 25 = (N + 1) + 24 by omega, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by positivity)

theorem exists_schwartzCommutator_sampling_bound (N : ℕ) (K : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      Summable (expandingCommutatorMoment L N (schwartzLatticeCoefficient L K)) ∧
        (∑' m, expandingCommutatorMoment L N (schwartzLatticeCoefficient L K) m) ≤ C := by
  obtain ⟨D, hD, hd⟩ := schwartzCommutator_decay N K
  refine ⟨((2 * Real.pi) ^ (12 : ℕ))⁻¹ * D * (1 + 2 * Real.pi) ^ (12 : ℕ), by positivity, ?_⟩
  intro L hL
  have hLp : 0 < L := by linarith
  let A : ℝ := ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ * D
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨hs, hb⟩ := scaledRadialKernel_sum L hL
  have hm (m : frequencyLattice) : expandingCommutatorMoment L N (schwartzLatticeCoefficient L K) m ≤
      A * ((1 + ‖(L⁻¹ : ℝ) • (m : E)‖ ^ 2) ^ (12 : ℕ))⁻¹ := by
    have hn : ‖(L⁻¹ : ℝ) • (m : E)‖ = ‖m‖ / L := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hLp, Submodule.norm_coe, div_eq_inv_mul]
    have he := mul_le_mul_of_nonneg_left (hd ((L⁻¹ : ℝ) • (m : E)))
      (show 0 ≤ ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ by positivity)
    rw [hn] at he
    dsimp only [expandingCommutatorMoment, schwartzLatticeCoefficient, A]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hn]
    convert he using 1 <;> ring
  have hsum := Summable.of_nonneg_of_le
    (expandingCommutatorMoment_nonneg L hL N (schwartzLatticeCoefficient L K)) hm (hs.mul_left A)
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' m : frequencyLattice, A * ((1 + ‖(L⁻¹ : ℝ) • (m : E)‖ ^ 2) ^ (12 : ℕ))⁻¹ :=
      hsum.tsum_le_tsum hm (hs.mul_left A)
    _ = A * ∑' m : frequencyLattice, ((1 + ‖(L⁻¹ : ℝ) • (m : E)‖ ^ 2) ^ (12 : ℕ))⁻¹ := tsum_mul_left
    _ ≤ A * (((1 + 2 * Real.pi) * L) ^ (12 : ℕ)) := mul_le_mul_of_nonneg_left hb hA
    _ = _ := by dsimp only [A]; rw [mul_pow, mul_pow]; field_simp

end DefocusingNLS

end OAI
