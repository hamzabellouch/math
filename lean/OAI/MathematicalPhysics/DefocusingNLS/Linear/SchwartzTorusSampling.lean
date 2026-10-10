import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzLatticeSampling
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingTorus

namespace OAI

/-! # Schwartz Fourier sampling in the exact expanding-torus space

The sampled coefficients carry the physical volume factor `(2πL)⁻¹²`.
Their exact `Y_L` vectors have norms bounded independently of `L ≥ 1`.
-/

open scoped SchwartzMap ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def schwartzLatticeCoefficient (L : ℝ) (K : 𝓢(E, ℂ))
    (n : frequencyLattice) : ℂ :=
  (((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ : ℝ) * K ((L⁻¹ : ℝ) • (n : E))

noncomputable def weightedSchwartzLatticeCoefficient (a k L : ℝ) (K : 𝓢(E, ℂ))
    (n : frequencyLattice) : ℂ :=
  (expandingSobolevWeight a k L n : ℂ) * schwartzLatticeCoefficient L K n

theorem weightedSchwartzLatticeCoefficient_norm_sq (a k L : ℝ) (hL : 1 ≤ L)
    (K : 𝓢(E, ℂ)) (n : frequencyLattice) :
    ‖weightedSchwartzLatticeCoefficient a k L K n‖ ^ 2 =
      ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ *
        ((L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) + (‖n‖ / L) ^ (2 * k)) *
          ‖K ((L⁻¹ : ℝ) • (n : E))‖ ^ 2 := by
  have hLp : 0 < L := by linarith
  have hP : 0 < (2 * Real.pi * L) ^ (12 : ℕ) := by positivity
  have hw : expandingSobolevWeight a k L n ^ 2 =
      (2 * Real.pi * L) ^ (12 : ℕ) *
        ((L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) + (‖n‖ / L) ^ (2 * k)) := by
    rw [expandingSobolevWeight_sq a k L hL]
    exact (expandingSobolevWeightSq_original a k L hL n).symm
  have hc : ‖schwartzLatticeCoefficient L K n‖ ^ 2 =
      (((2 * Real.pi * L) ^ (12 : ℕ))⁻¹) ^ 2 *
        ‖K ((L⁻¹ : ℝ) • (n : E))‖ ^ 2 := by
    change ‖(((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ : ℝ) •
      K ((L⁻¹ : ℝ) • (n : E))‖ ^ 2 = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hP), mul_pow]
  unfold weightedSchwartzLatticeCoefficient
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (expandingSobolevWeight_pos a k L hL n), mul_pow, hc, hw]
  field_simp

private theorem sampling_density_le (a k L : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (hL : 1 ≤ L) (n : frequencyLattice) :
    (L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) + (‖n‖ / L) ^ (2 * k) ≤
      (1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ (6 - a) +
        (1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ k := by
  have hLp : 0 < L := by linarith
  have hn : ‖(L⁻¹ : ℝ) • (n : E)‖ = ‖n‖ / L := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hLp, div_eq_inv_mul,
      Submodule.norm_coe]
  rw [hn]
  apply add_le_add
  · exact Real.rpow_le_rpow (by positivity)
      (add_le_add (Real.rpow_le_one_of_one_le_of_nonpos (z := -2) hL (by norm_num)) le_rfl)
      (by linarith)
  · calc
      _ = ((‖n‖ / L) ^ (2 : ℕ)) ^ k := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ (1 + (‖n‖ / L) ^ (2 : ℕ)) ^ k :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)

theorem exists_weightedSchwartz_torus_sampling_bound (a k : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (K : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      Summable (fun n => ‖weightedSchwartzLatticeCoefficient a k L K n‖ ^ 2) ∧
        (∑' n, ‖weightedSchwartzLatticeCoefficient a k L K n‖ ^ 2) ≤ C := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_weightedSchwartz_scaledLattice_l2_bound (6 - a) K
  obtain ⟨C₁, hC₁, h₁⟩ := exists_weightedSchwartz_scaledLattice_l2_bound k K
  refine ⟨((2 * Real.pi) ^ (12 : ℕ))⁻¹ * (C₀ + C₁), by positivity, ?_⟩
  intro L hL
  have hLp : 0 < L := by linarith
  obtain ⟨hs₀, hb₀⟩ := h₀ L hL
  obtain ⟨hs₁, hb₁⟩ := h₁ L hL
  let g : frequencyLattice → ℝ := fun n =>
    (1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ (6 - a) * ‖K ((L⁻¹ : ℝ) • (n : E))‖ ^ 2 +
      (1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ k * ‖K ((L⁻¹ : ℝ) • (n : E))‖ ^ 2
  have hgs : Summable g := hs₀.add hs₁
  have hgb : (∑' n, g n) ≤ (C₀ + C₁) * L ^ (12 : ℕ) := by
    dsimp only [g]
    rw [hs₀.tsum_add hs₁]
    nlinarith
  have hmajor (n : frequencyLattice) :
      ‖weightedSchwartzLatticeCoefficient a k L K n‖ ^ 2 ≤
        ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ * g n := by
    rw [weightedSchwartzLatticeCoefficient_norm_sq a k L hL]
    have h := mul_le_mul_of_nonneg_right (sampling_density_le a k L ha1 hk hL n)
      (sq_nonneg ‖K ((L⁻¹ : ℝ) • (n : E))‖)
    simpa only [g, add_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹)
  have hs := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hmajor
    (hgs.mul_left (((2 * Real.pi * L) ^ (12 : ℕ))⁻¹))
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n, ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ * g n :=
      hs.tsum_le_tsum hmajor (hgs.mul_left _)
    _ = ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ * ∑' n, g n := tsum_mul_left
    _ ≤ ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ * ((C₀ + C₁) * L ^ (12 : ℕ)) :=
      mul_le_mul_of_nonneg_left hgb (by positivity)
    _ = _ := by
      rw [mul_pow]
      field_simp

noncomputable def schwartzTorusSample (a k L : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (hL : 1 ≤ L) (K : 𝓢(E, ℂ)) : FourierL2 :=
  ⟨weightedSchwartzLatticeCoefficient a k L K, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      ((exists_weightedSchwartz_torus_sampling_bound a k ha1 hk K).choose_spec.2 L hL).1⟩

theorem schwartzTorusSample_coefficient (a k L : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (hL : 1 ≤ L) (K : 𝓢(E, ℂ)) (n : frequencyLattice) :
    expandingFourierCoefficient a k L (schwartzTorusSample a k L ha1 hk hL K) n =
      schwartzLatticeCoefficient L K n := by
  change (((expandingSobolevWeight a k L n)⁻¹ : ℝ) : ℂ) *
      ((expandingSobolevWeight a k L n : ℂ) * schwartzLatticeCoefficient L K n) = _
  rw [← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (expandingSobolevWeight_pos a k L hL n).ne']
  simp

theorem exists_schwartzTorusSample_norm_bound (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (K : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, ∀ hL : 1 ≤ L,
      ‖schwartzTorusSample a k L ha1 hk hL K‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_weightedSchwartz_torus_sampling_bound a k ha1 hk K
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro L hL
  have hn := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (schwartzTorusSample a k L ha1 hk hL K)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
  have hsq : ‖schwartzTorusSample a k L ha1 hk hL K‖ ^ 2 ≤ C := by
    rw [hn]
    exact (hb L hL).2
  nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C,
    norm_nonneg (schwartzTorusSample a k L ha1 hk hL K)]

theorem schwartzTorusSample_function (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (K : 𝓢(E, ℂ)) (x : SchrodingerTorus) :
    expandingTorusFunction a k L (schwartzTorusSample a k L ha1 hk hL K) x =
      ∑' n, schwartzLatticeCoefficient L K n * torusCharacter n x := by
  rw [expandingTorusFunction_apply a k L ha ha1 hk hL]
  simp only [schwartzTorusSample_coefficient]

end DefocusingNLS

end OAI
