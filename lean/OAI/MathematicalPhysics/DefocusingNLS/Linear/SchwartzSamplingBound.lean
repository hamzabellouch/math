import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzTorusSampling

namespace OAI

/-! # Quantitative Schwartz sampling bounds

The constant is independent of both the expanding scale and the Schwartz
kernel.  Dependence on the kernel is isolated in two weighted decay bounds.
-/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem schwartz_scaledLattice_l2_bound_of_decay (K : 𝓢(E, ℂ))
    (D : ℝ) (_hD : 0 ≤ D)
    (hb : ∀ x : E, (1 + ‖x‖) ^ (12 : ℕ) * ‖K x‖ ≤ D)
    (L : ℝ) (hL : 1 ≤ L) :
    Summable (fun n : frequencyLattice => ‖K (L⁻¹ • (n : E))‖ ^ 2) ∧
      (∑' n : frequencyLattice, ‖K (L⁻¹ • (n : E))‖ ^ 2) ≤
        D ^ 2 * (1 + 2 * Real.pi) ^ (12 : ℕ) * L ^ (12 : ℕ) := by
  have hdecay (x : E) :
      ‖K x‖ ^ 2 ≤ D ^ 2 * ((1 + ‖x‖ ^ 2) ^ (12 : ℕ))⁻¹ := by
    have hw : (1 + ‖x‖ ^ 2) ^ 6 ≤ (1 + ‖x‖) ^ 12 := by
      calc
        _ ≤ ((1 + ‖x‖) ^ 2) ^ 6 :=
          pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg x]) _
        _ = _ := by ring
    have he := (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans (hb x)
    have hs := pow_le_pow_left₀
      (by positivity : 0 ≤ (1 + ‖x‖ ^ 2) ^ 6 * ‖K x‖) he 2
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0 < (1 + ‖x‖ ^ 2) ^ (12 : ℕ))).mpr
    nlinarith [show ((1 + ‖x‖ ^ 2) ^ 6 * ‖K x‖) ^ 2 =
      ‖K x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (12 : ℕ) by ring]
  obtain ⟨hs, hsum⟩ := scaledRadialKernel_sum L hL
  have hmajor := hs.mul_left (D ^ 2)
  have hS : Summable (fun n : frequencyLattice => ‖K (L⁻¹ • (n : E))‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => hdecay _) hmajor
  refine ⟨hS, ?_⟩
  calc
    _ ≤ ∑' n : frequencyLattice,
        D ^ 2 * ((1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ (12 : ℕ))⁻¹ :=
      hS.tsum_le_tsum (fun n => hdecay _) hmajor
    _ = D ^ 2 * ∑' n : frequencyLattice,
        ((1 + ‖(L⁻¹ : ℝ) • (n : E)‖ ^ 2) ^ (12 : ℕ))⁻¹ := tsum_mul_left
    _ ≤ D ^ 2 * (((1 + 2 * Real.pi) * L) ^ (12 : ℕ)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg D)
    _ = _ := by rw [mul_pow]; ring

theorem weightedSchwartz_scaledLattice_bound_of_decay (s : ℝ) (K : 𝓢(E, ℂ))
    (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ x : E, (1 + ‖x‖) ^ (12 : ℕ) * ‖weightedSchwartzKernel s K x‖ ≤ D)
    (L : ℝ) (hL : 1 ≤ L) :
    Summable (fun n : frequencyLattice =>
      (1 + ‖L⁻¹ • (n : E)‖ ^ 2) ^ s * ‖K (L⁻¹ • (n : E))‖ ^ 2) ∧
      (∑' n : frequencyLattice,
        (1 + ‖L⁻¹ • (n : E)‖ ^ 2) ^ s * ‖K (L⁻¹ • (n : E))‖ ^ 2) ≤
        D ^ 2 * (1 + 2 * Real.pi) ^ (12 : ℕ) * L ^ (12 : ℕ) := by
  have he (x : E) : ‖weightedSchwartzKernel s K x‖ ^ 2 =
      (1 + ‖x‖ ^ 2) ^ s * ‖K x‖ ^ 2 := by
    rw [weightedSchwartzKernel_norm, mul_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    congr 2
    ring
  simpa only [he] using
    schwartz_scaledLattice_l2_bound_of_decay (weightedSchwartzKernel s K) D hD hb L hL

theorem schwartzTorusSample_norm_le_of_weighted_decay (a k : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (K : 𝓢(E, ℂ)) (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ s ∈ ({6 - a, k} : Set ℝ), ∀ x : E,
      (1 + ‖x‖) ^ (12 : ℕ) * ‖weightedSchwartzKernel s K x‖ ≤ D)
    (L : ℝ) (hL : 1 ≤ L) :
    ‖schwartzTorusSample a k L ha1 hk hL K‖ ≤
      Real.sqrt (2 * ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
        (1 + 2 * Real.pi) ^ (12 : ℕ)) * D := by
  have hLp : 0 < L := by linarith
  obtain ⟨hs₀, hb₀⟩ := weightedSchwartz_scaledLattice_bound_of_decay
    (6 - a) K D hD (hb _ (by simp)) L hL
  obtain ⟨hs₁, hb₁⟩ := weightedSchwartz_scaledLattice_bound_of_decay
    k K D hD (hb _ (by simp)) L hL
  let g : frequencyLattice → ℝ := fun n =>
    (1 + ‖L⁻¹ • (n : E)‖ ^ 2) ^ (6 - a) * ‖K (L⁻¹ • (n : E))‖ ^ 2 +
      (1 + ‖L⁻¹ • (n : E)‖ ^ 2) ^ k * ‖K (L⁻¹ • (n : E))‖ ^ 2
  have hgs : Summable g := hs₀.add hs₁
  have hgb : (∑' n, g n) ≤
      2 * D ^ 2 * (1 + 2 * Real.pi) ^ (12 : ℕ) * L ^ (12 : ℕ) := by
    dsimp only [g]
    rw [hs₀.tsum_add hs₁]
    linarith
  have hdensity (n : frequencyLattice) :
      (L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) + (‖n‖ / L) ^ (2 * k) ≤
        (1 + ‖L⁻¹ • (n : E)‖ ^ 2) ^ (6 - a) +
          (1 + ‖L⁻¹ • (n : E)‖ ^ 2) ^ k := by
    have hn : ‖(L⁻¹ : ℝ) • (n : E)‖ = ‖n‖ / L := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hLp, div_eq_inv_mul,
        Submodule.norm_coe]
    rw [hn]
    apply add_le_add
    · exact Real.rpow_le_rpow (by positivity)
        (add_le_add (Real.rpow_le_one_of_one_le_of_nonpos (z := -2) hL (by norm_num))
          le_rfl) (by linarith)
    · calc
        _ = ((‖n‖ / L) ^ (2 : ℕ)) ^ k := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num
        _ ≤ (1 + (‖n‖ / L) ^ (2 : ℕ)) ^ k :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hmajor (n : frequencyLattice) :
      ‖weightedSchwartzLatticeCoefficient a k L K n‖ ^ 2 ≤
        ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ * g n := by
    rw [weightedSchwartzLatticeCoefficient_norm_sq a k L hL]
    have h := mul_le_mul_of_nonneg_right (hdensity n)
      (sq_nonneg ‖K ((L⁻¹ : ℝ) • (n : E))‖)
    simpa only [g, add_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹)
  have hs := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hmajor
    (hgs.mul_left (((2 * Real.pi * L) ^ (12 : ℕ))⁻¹))
  have hsum : (∑' n, ‖weightedSchwartzLatticeCoefficient a k L K n‖ ^ 2) ≤
      (2 * ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * (1 + 2 * Real.pi) ^ (12 : ℕ)) * D ^ 2 := by
    calc
      _ ≤ ∑' n, ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ * g n :=
        hs.tsum_le_tsum hmajor (hgs.mul_left _)
      _ = ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ * ∑' n, g n := tsum_mul_left
      _ ≤ ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ *
          (2 * D ^ 2 * (1 + 2 * Real.pi) ^ (12 : ℕ) * L ^ (12 : ℕ)) :=
        mul_le_mul_of_nonneg_left hgb (by positivity)
      _ = _ := by rw [mul_pow]; field_simp
  have hn := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (schwartzTorusSample a k L ha1 hk hL K)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
  change ‖schwartzTorusSample a k L ha1 hk hL K‖ ^ 2 =
    (∑' n, ‖weightedSchwartzLatticeCoefficient a k L K n‖ ^ 2) at hn
  have hc : 0 ≤ 2 * ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
      (1 + 2 * Real.pi) ^ (12 : ℕ) := by positivity
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hD)).mp
  rw [mul_pow, Real.sq_sqrt hc, hn]
  exact hsum

end DefocusingNLS

end OAI
