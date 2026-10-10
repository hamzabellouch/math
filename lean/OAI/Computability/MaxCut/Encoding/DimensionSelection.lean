import Mathlib
import OAI.Computability.MaxCut.Games.MatrixGap

namespace OAI

/-! Logical dimension is chosen after the inverse density and row bound,
and before the tuple length. All row maps, including deficient-rank maps,
satisfy the resulting small trivial-character bound. -/

namespace MaxCutGames.Decoder.DimensionSelection

noncomputable section

theorem exists_logical_dimension {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (r lower : ℕ) :
    ∃ ell : ℕ, lower ≤ ell ∧ r < ell ∧
      1 / (2 : ℝ) ^ (ell - r) < α / 8 ∧
      1 / (2 : ℝ) ^ ell < η / 4 := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (lt_min (show (0 : ℝ) < α / 8 by positivity)
      (show (0 : ℝ) < η / 4 by positivity))
    (show (1 / 2 : ℝ) < 1 by norm_num)
  let ell := max lower (r + n + 1)
  have hrn : r + n + 1 ≤ ell := le_max_right _ _
  have hr : r < ell := lt_of_lt_of_le (by omega) hrn
  have hnsub : n ≤ ell - r := by omega
  have hnell : n ≤ ell := hnsub.trans (Nat.sub_le _ _)
  have hpow (j : ℕ) (hj : n ≤ j) :
      1 / (2 : ℝ) ^ j < min (α / 8) (η / 4) := by
    have hmon : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    simpa only [one_div, inv_pow] using hmon.trans_lt hn
  exact ⟨ell, le_max_left _ _, hr,
    (hpow (ell - r) hnsub).trans_le (min_le_left _ _),
    (hpow ell hnell).trans_le (min_le_right _ _)⟩

/-- Uniform choice of `ell` bounds the trivial character fraction for every
possible public row map without conditioning on its rank. -/
theorem kernel_fraction_le {ell r : ℕ}
    (A : (Fin ell → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) [Fintype A.ker] :
    1 / (Fintype.card A.ker : ℝ) ≤ 1 / (2 : ℝ) ^ (ell - r) := by
  have hcard : (2 : ℝ) ^ (ell - r) ≤ (Fintype.card A.ker : ℝ) := by
    have h := Inverse.binary_kernel_card_lower A
    rw [Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  exact one_div_le_one_div_of_le (by positivity) hcard

theorem kernel_fraction_lt {ell r : ℕ} {α : ℝ}
    (A : (Fin ell → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) [Fintype A.ker]
    (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    1 / (Fintype.card A.ker : ℝ) < α / 8 :=
  (kernel_fraction_le A).trans_lt hsmall

end
end MaxCutGames.Decoder.DimensionSelection

/-!
# Finite latent samplers and their actual spectral law

This bridge counts all sampler outcomes, including repeated vectors and the
zero vector.  Uniform sampler detection is exactly the complement of the
matrix operator's annihilation multiplier.
-/

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixNoise

namespace MaxCutGames.Decoder.NoiseSampler

section FiniteLaw

variable {Noise V : Type*} [Fintype Noise] [Fintype V]

/-- The real pushforward of the uniform law on sampler outcomes. -/
def samplerLaw (noise : Noise → V) (v : V) : ℝ := by
  classical
  exact ∑ n, if noise n = v then (Fintype.card Noise : ℝ)⁻¹ else 0

omit [Fintype V] in
theorem samplerLaw_nonneg (noise : Noise → V) (v : V) :
    0 ≤ samplerLaw noise v := by
  classical
  unfold samplerLaw
  apply Finset.sum_nonneg
  intro n _
  split_ifs <;> positivity

omit [Fintype V] in
/-- Literal counting formula; multiple sampler outcomes mapping to the same
vector retain their multiplicity. -/
theorem samplerLaw_eq_count (noise : Noise → V) (v : V) :
    samplerLaw noise v =
      ((Finset.univ.filter fun n => noise n = v).card : ℝ) / Fintype.card Noise := by
  classical
  unfold samplerLaw
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

theorem samplerLaw_sum (noise : Noise → V) (f : V → ℝ) :
    (∑ v, samplerLaw noise v * f v) =
      (Fintype.card Noise : ℝ)⁻¹ * ∑ n, f (noise n) := by
  classical
  unfold samplerLaw
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact (Finset.mul_sum _ _ _).symm

/-- Exact pushforward expectation, with the uniform normalization explicit. -/
theorem sample_expect_eq (noise : Noise → V) (f : V → ℝ) :
    (𝔼 n, f (noise n)) = ∑ v, samplerLaw noise v * f v := by
  rw [samplerLaw_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv, mul_comm]

theorem samplerLaw_normalized [Nonempty Noise] (noise : Noise → V) :
    ∑ v, samplerLaw noise v = 1 := by
  have h := sample_expect_eq noise (fun _ => 1)
  simpa using h.symm

theorem rat_expect_cast (f : Noise → ℚ) :
    ((𝔼 n, f n : ℚ) : ℝ) = 𝔼 n, (f n : ℝ) := by
  simp only [Finset.expect_eq_sum_div_card, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]

omit [Fintype V] in
theorem samplerLaw_eq_rat_count (noise : Noise → V) (v : V) :
    samplerLaw noise v =
      ((((Finset.univ.filter fun n => noise n = v).card : ℚ) /
        (Fintype.card Noise : ℚ) : ℚ) : ℝ) := by
  rw [samplerLaw_eq_count]
  simp only [Rat.cast_div, Rat.cast_natCast]

end FiniteLaw

variable {Noise V E : Type*} [Fintype Noise] [Fintype V]
  [AddCommGroup V] [Module F2 V]
  [AddCommGroup E] [Module F2 E]

/-- The actual matrix multiplier is precisely the sampler's kernel event. -/
theorem sample_kernel_eq_eigenvalue (noise : Noise → V) (S : V →ₗ[F2] E) :
    (𝔼 n, if S (noise n) = 0 then (1 : ℝ) else 0) =
      linearNoiseEigenvalue (samplerLaw noise) S := by
  classical
  exact sample_expect_eq noise (fun v => if S v = 0 then 1 else 0)

/-- Detection plus annihilation is one for the same unconditional sampler. -/
theorem detection_add_eigenvalue [Nonempty Noise]
    (noise : Noise → V) (S : V →ₗ[F2] E) :
    (𝔼 n, if S (noise n) ≠ 0 then (1 : ℝ) else 0) +
      linearNoiseEigenvalue (samplerLaw noise) S = 1 := by
  classical
  rw [← sample_kernel_eq_eigenvalue, ← Finset.expect_add_distrib]
  calc
    _ = 𝔼 _n : Noise, (1 : ℝ) := by
      apply Finset.expect_congr rfl
      intro n _
      by_cases h : S (noise n) = 0 <;> simp [h]
    _ = 1 := Fintype.expect_const 1

/-- The constant-detection input becomes the `7/8` multiplier bound. -/
theorem detection_eigenvalue_le [Nonempty Noise]
    (noise : Noise → V) (S : V →ₗ[F2] E)
    (hdetect : (1 : ℝ) / 8 ≤ 𝔼 n, if S (noise n) ≠ 0 then (1 : ℝ) else 0) :
    linearNoiseEigenvalue (samplerLaw noise) S ≤ 7 / 8 := by
  have h := detection_add_eigenvalue noise S
  linarith

/-- The generic detection level is also retained for future parameter changes. -/
theorem detection_eigenvalue_le_complement [Nonempty Noise]
    (noise : Noise → V) (S : V →ₗ[F2] E) (d : ℝ)
    (hdetect : d ≤ 𝔼 n, if S (noise n) ≠ 0 then (1 : ℝ) else 0) :
    linearNoiseEigenvalue (samplerLaw noise) S ≤ 1 - d := by
  have h := detection_add_eigenvalue noise S
  linarith

/-- The gadget may keep its finite probabilities rational throughout. -/
theorem rational_detection_eigenvalue_le [Nonempty Noise]
    (noise : Noise → V) (S : V →ₗ[F2] E)
    (hdetect : (1 : ℚ) / 8 ≤ 𝔼 n, if S (noise n) ≠ 0 then (1 : ℚ) else 0) :
    linearNoiseEigenvalue (samplerLaw noise) S ≤ 7 / 8 := by
  apply detection_eigenvalue_le noise S
  have hcast := (Rat.cast_le (K := ℝ)).mpr hdetect
  rw [rat_expect_cast] at hcast
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero,
    apply_ite] using hcast

end MaxCutGames.Decoder.NoiseSampler
end

end OAI
