import OAI.NumberTheory.Ostmann.Quadratic.QuadraticResidueDecomposition
import OAI.NumberTheory.Ostmann.Characters.SquarePullbackNorm

namespace OAI

/-! # A large original quadratic sum forces a large residue progression -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadraticResidueAmplitude_mass {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0)
    (henergy : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (a : ZMod q) (h₀ s v : ℕ) :
    (∑ r : ZMod q, ‖quadraticResidueAmplitude g a h₀ s v r‖) ≤
      Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) * q := by
  simp only [quadraticResidueAmplitude_norm]
  have he (r : ZMod q) : a * r ^ 2 * (s : ZMod q) = (a * s) * r ^ 2 := by ring
  simp_rw [he]
  exact square_pullback_norm_le q g hg henergy (a * s)

theorem quadraticDensitySum_large_residue {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0)
    (henergy : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (W : Finset ℕ) (a : ZMod q) (h₀ s v : ℕ) (θ R A : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) (hA : 0 ≤ A)
    (hlarge : (Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) * q) * A <
      Real.sqrt (R * q / ((s : ℝ) * v)) *
        ‖quadraticDensitySum g W a ((h₀ : ℝ) + θ) Φ R v s‖) :
    ∃ r : ZMod q, A < ‖∑ w ∈ W.filter (fun w : ℕ => (w : ZMod q) = r),
      quadraticResidueWave (q := q) θ Φ R s v w‖ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hQ : 0 < Real.sqrt (R * q / ((s : ℝ) * v)) := Real.sqrt_pos.mpr (by positivity)
  rw [quadraticDensitySum_residue_decomposition, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hQ, ← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul] at hlarge
  by_contra! hn
  have hb : ‖∑ r : ZMod q, quadraticResidueAmplitude g a h₀ s v r *
      ∑ w ∈ W.filter (fun w : ℕ => (w : ZMod q) = r),
        quadraticResidueWave (q := q) θ Φ R s v w‖ ≤
      (Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) * q) * A := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ r : ZMod q, ‖quadraticResidueAmplitude g a h₀ s v r‖ * A := by
        apply Finset.sum_le_sum
        intro r _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hn r) (norm_nonneg _)
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (quadraticResidueAmplitude_mass g hg henergy a h₀ s v) hA
  exact (not_lt_of_ge hb) hlarge

end Ostmann

end OAI
