import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPhysicalSampling
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingNonlinearity

namespace OAI

/-! # Odd-power nonlinearity commutes with the cutoff periodization

The support radius is at most twice the scale, whereas distinct lattice
translates are separated by at least `2π` times the scale.
-/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem oddPowerNonlinearity_tsum_disjoint {ι : Type*} (m : ℕ) (f : ι → ℂ)
    (hd : ∀ i j, i ≠ j → f i = 0 ∨ f j = 0) :
    oddPowerNonlinearity m (∑' i, f i) = ∑' i, oddPowerNonlinearity m (f i) := by
  classical
  by_cases hz : ∀ i, f i = 0
  · simp [hz, oddPowerNonlinearity]
  · push Not at hz
    obtain ⟨i, hi⟩ := hz
    have hj (j : ι) (hji : j ≠ i) : f j = 0 :=
      (hd j i hji).resolve_right hi
    rw [tsum_eq_single i hj, tsum_eq_single i]
    intro j hji
    simp [hj j hji, oddPowerNonlinearity]

theorem cutoff_periodization_disjoint (L : ℝ) (hL : 0 < L) (ψ : E → ℂ)
    (hψ : ∀ x : E, 2 * L < ‖x‖ → ψ x = 0) (y : E)
    (n m : frequencyLattice) (hnm : n ≠ m) :
    ψ (y + (2 * Real.pi * L) • (n : E)) = 0 ∨
      ψ (y + (2 * Real.pi * L) • (m : E)) = 0 := by
  by_contra! hne
  have hn : ‖y + (2 * Real.pi * L) • (n : E)‖ ≤ 2 * L := by
    by_contra h
    exact hne.1 (hψ _ (lt_of_not_ge h))
  have hm : ‖y + (2 * Real.pi * L) • (m : E)‖ ≤ 2 * L := by
    by_contra h
    exact hne.2 (hψ _ (lt_of_not_ge h))
  have hd : 1 ≤ ‖n - m‖ := one_le_norm_frequencyLattice (sub_ne_zero.mpr hnm)
  have hp : 0 < 2 * Real.pi * L := by positivity
  have hlarge : 2 * Real.pi * L ≤ ‖(2 * Real.pi * L) • ((n - m : frequencyLattice) : E)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, Submodule.norm_coe]
    exact le_mul_of_one_le_right hp.le hd
  have he : (2 * Real.pi * L) • ((n - m : frequencyLattice) : E) =
      (y + (2 * Real.pi * L) • (n : E)) -
        (y + (2 * Real.pi * L) • (m : E)) := by
    simp only [Submodule.coe_sub, smul_sub]
    abel
  rw [he] at hlarge
  have hsmall := norm_sub_le (y + (2 * Real.pi * L) • (n : E))
    (y + (2 * Real.pi * L) • (m : E))
  nlinarith [Real.pi_gt_three]

theorem oddPowerNonlinearity_periodization (m : ℕ) (L : ℝ) (hL : 0 < L)
    (ψ : E → ℂ) (hψ : ∀ x : E, 2 * L < ‖x‖ → ψ x = 0) (y : E) :
    oddPowerNonlinearity m (∑' n : frequencyLattice,
      ψ (y + (2 * Real.pi * L) • (n : E))) =
      ∑' n : frequencyLattice,
        oddPowerNonlinearity m (ψ (y + (2 * Real.pi * L) • (n : E))) :=
  oddPowerNonlinearity_tsum_disjoint m _ (cutoff_periodization_disjoint L hL ψ hψ y)

/-- The actual torus polynomial is the periodization of the physical polynomial. -/
theorem sampled_oddPower_periodization (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (m : ℕ) (ψ : 𝓢(E, ℂ)) (hψ : ∀ x : E, 2 * L < ‖x‖ → ψ x = 0) (y : E) :
    expandingTorusFunction a k L
      (expandingOddPower a k L ha ha1 hk hL m
        (schwartzTorusSample a k L ha1 hk hL (radianFourierKernel ψ)))
      (euclideanToTorus (L⁻¹ • y)) =
      ∑' n : frequencyLattice,
        oddPowerNonlinearity m (ψ (y + (2 * Real.pi * L) • (n : E))) := by
  rw [expandingOddPower_apply, schwartzTorusSample_physical a k L ha ha1 hk hL]
  exact oddPowerNonlinearity_periodization m L (lt_of_lt_of_le zero_lt_one hL) ψ hψ y

end DefocusingNLS

end OAI
