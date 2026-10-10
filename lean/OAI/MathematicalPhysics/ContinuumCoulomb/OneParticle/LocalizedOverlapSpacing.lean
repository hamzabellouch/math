import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedOrbitalGram

namespace OAI

/-! One fixed logarithmic spacing controls actual orbital Gram row sums
for all polynomial site counts, with no independent small-overlap premise. -/

noncomputable section
namespace ContinuumCoulomb

theorem localizedOverlapBound_log (k : ℕ) {N : ℝ} (hN : 0 < N) :
    localizedOverlapBound (((10 * k : ℕ) : ℝ) * Real.log N) = planarOverlapConstant / N ^ (9 * k) := by
  unfold localizedOverlapBound
  rw [show -(9 / 10 : ℝ) * (((10 * k : ℕ) : ℝ) * Real.log N) =
    -(((9 * k : ℕ) : ℝ) * Real.log N) by push_cast; ring,
    Real.exp_neg, Real.exp_nat_mul, Real.exp_log hN]
  rfl

theorem exists_localizedOverlap_spacing (A : ℕ) :
    ∃ k : ℕ, 0 < k ∧ ∀ N : ℝ, 2 ≤ N →
      N ^ A * localizedOverlapBound ((k : ℝ) * Real.log N) ≤ 1 / 2 := by
  obtain ⟨q, hq⟩ := exists_nat_ge (max 1 (2 * planarOverlapConstant))
  have hq₁ : (1 : ℝ) ≤ q := (le_max_left _ _).trans hq
  have hqC : 2 * planarOverlapConstant ≤ (q : ℝ) := (le_max_right _ _).trans hq
  have hqp : 0 < q := by exact_mod_cast (by linarith : (0 : ℝ) < q)
  refine ⟨10 * (A + q), by omega, fun N hN => ?_⟩
  have hNp : 0 < N := by linarith
  have hpow : (q : ℝ) ≤ N ^ q := by
    have h : (q : ℝ) ≤ (2 : ℝ) ^ q := by exact_mod_cast (Nat.lt_two_pow_self (n := q)).le
    exact h.trans (pow_le_pow_left₀ (by norm_num) hN q)
  have hC : planarOverlapConstant / N ^ q ≤ 1 / 2 := by
    apply (div_le_iff₀ (pow_pos hNp q)).mpr
    linarith [hqC.trans hpow]
  rw [localizedOverlapBound_log (A + q) hNp]
  have hlarge : N ^ (A + q) ≤ N ^ (9 * (A + q)) :=
    pow_le_pow_right₀ (by linarith : 1 ≤ N) (by omega)
  have hdiv := div_le_div_of_nonneg_left planarOverlapConstant_nonnegative (pow_pos hNp (A + q)) hlarge
  calc
    _ ≤ N ^ A * (planarOverlapConstant / N ^ (A + q)) :=
      mul_le_mul_of_nonneg_left hdiv (pow_nonneg hNp.le A)
    _ = planarOverlapConstant / N ^ q := by
      rw [pow_add]
      field_simp [pow_ne_zero A hNp.ne', pow_ne_zero q hNp.ne']
    _ ≤ _ := hC

theorem exists_uniform_localizedOrbitals (A : ℕ) :
    ∃ k : ℕ, 0 < k ∧ ∀ (N : ℝ), 2 ≤ N → ∀ (m : ℕ), (m : ℝ) ≤ N ^ A →
      ∀ (u : Fin m → PlanarPosition), (∀ i j, i ≠ j → (k : ℝ) * Real.log N ≤ ‖u i - u j‖) →
      ∀ (freq : ℝ) (hfreq : 0 < freq),
        LinearIndependent ℝ (fun i => localizedOrbitalL2 hfreq (u i)) ∧
        Orthonormal ℝ (orthonormalLocalizedOrbitals hfreq u) := by
  obtain ⟨k, hk, hspacing⟩ := exists_localizedOverlap_spacing A
  refine ⟨k, hk, fun N hN m hm u hsep freq hfreq => ?_⟩
  have hsmall : m * localizedOverlapBound ((k : ℝ) * Real.log N) < 1 := by
    have h := (mul_le_mul_of_nonneg_right hm (localizedOverlapBound_nonnegative _)).trans (hspacing N hN)
    linarith
  exact ⟨localizedOrbitalL2_linearIndependent hfreq u hsep hsmall,
    orthonormalLocalizedOrbitals_orthonormal hfreq u hsep hsmall⟩

end ContinuumCoulomb

end

end OAI
