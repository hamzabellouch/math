import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombCalibration

namespace OAI

/-! Fixed positive analytic constants fit uniform polynomial ranges for
every size parameter at least two. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_polynomial_constant_bounds {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∃ q : ℕ, 0 < q ∧ ∀ N : ℝ, 2 ≤ N → (N ^ q)⁻¹ ≤ c ∧ C ≤ N ^ q := by
  obtain ⟨q, hq⟩ := exists_nat_ge (max 1 (max (1 / c) C))
  have hq₁ : (1 : ℝ) ≤ q := (le_max_left _ _).trans hq
  have hqc : 1 / c ≤ (q : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hq)
  have hqC : C ≤ (q : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hq)
  have hpow : (q : ℝ) ≤ (2 : ℝ) ^ q := by exact_mod_cast (Nat.lt_two_pow_self (n := q)).le
  refine ⟨q, by exact_mod_cast (by linarith : (0 : ℝ) < q), fun N hN => ?_⟩
  have hNp : 0 < N := by linarith
  have hp := hpow.trans (pow_le_pow_left₀ (by norm_num) hN q)
  refine ⟨?_, hqC.trans hp⟩
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (pow_pos hNp q)).mpr
  have h := (div_le_iff₀ hc).mp (hqc.trans hp)
  nlinarith only [h]

theorem sqrt_polynomial_bounds {N K : ℝ} {A : ℕ} (hN : 1 ≤ N)
    (hKlo : (N ^ A)⁻¹ ≤ K) (hKhi : K ≤ N ^ A) :
    (N ^ A)⁻¹ ≤ Real.sqrt K ∧ Real.sqrt K ≤ N ^ A := by
  have hp : 1 ≤ N ^ A := one_le_pow₀ hN
  have hp0 : 0 < N ^ A := by positivity
  have hi : 0 ≤ (N ^ A)⁻¹ := inv_nonneg.mpr hp0.le
  have hi₁ : (N ^ A)⁻¹ ≤ 1 := (inv_le_one₀ hp0).mpr hp
  constructor
  · apply Real.le_sqrt_of_sq_le
    exact (by nlinarith only [hi, hi₁] : ((N ^ A)⁻¹) ^ 2 ≤ (N ^ A)⁻¹).trans hKlo
  · apply Real.sqrt_le_iff.mpr
    exact ⟨hp0.le, hKhi.trans (by nlinarith only [hp])⟩

end ContinuumCoulomb

end

end OAI
