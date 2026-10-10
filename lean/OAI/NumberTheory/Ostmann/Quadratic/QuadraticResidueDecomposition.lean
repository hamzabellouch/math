import OAI.NumberTheory.Ostmann.Construction.OriginalQuadraticTerm
import OAI.NumberTheory.Ostmann.Characters.PeriodicLinearPhase

namespace OAI

/-! # Exact residue-class splitting before the inverse quadratic estimate -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem stdAddChar_nat_ratio {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = realAdditivePhase ((n : ℝ) / q) := by
  rw [← Int.cast_natCast, ZMod.stdAddChar_coe]
  unfold realAdditivePhase
  congr 1
  push_cast
  ring

theorem quadratic_phase_integer_part {q : ℕ} [NeZero q] (h₀ s v w : ℕ) (θ : ℝ) :
    realAdditivePhase (((h₀ : ℝ) + θ) * v * (w : ℝ) ^ 2 / q) ^ s =
      ZMod.stdAddChar (((h₀ * s * v : ℕ) : ZMod q) * (w : ZMod q) ^ 2) *
        realAdditivePhase (θ * s * v * (w : ℝ) ^ 2 / q) := by
  rw [original_quadratic_real_phase]
  have he : ((h₀ : ℝ) + θ) * s * v * (w : ℝ) ^ 2 / q =
      (h₀ : ℝ) * s * v * (w : ℝ) ^ 2 / q + θ * s * v * (w : ℝ) ^ 2 / q := by ring
  rw [he, realAdditivePhase_add]
  have hs := stdAddChar_nat_ratio (q := q) (h₀ * s * v * w ^ 2)
  push_cast at hs
  push_cast
  rw [hs]

noncomputable def quadraticResidueAmplitude {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (h₀ s v : ℕ) (r : ZMod q) : ℂ :=
  g (a * r ^ 2 * (s : ZMod q)) * ZMod.stdAddChar (((h₀ * s * v : ℕ) : ZMod q) * r ^ 2)

noncomputable def quadraticResidueWave {q : ℕ} (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R : ℝ) (s v w : ℕ) : ℂ :=
  realAdditivePhase (θ * s * v * (w : ℝ) ^ 2 / q) *
    Φ ((s : ℝ) * v * (w : ℝ) ^ 2 / (R * q))

theorem quadraticDensityTerm_residue_factor {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (h₀ s v w : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) :
    quadraticDensityTerm g a ((h₀ : ℝ) + θ) Φ R v s w =
      quadraticResidueAmplitude g a h₀ s v (w : ZMod q) *
        quadraticResidueWave (q := q) θ Φ R s v w := by
  rw [quadraticDensityTerm, quadratic_phase_integer_part]
  simp only [quadraticResidueAmplitude, quadraticResidueWave]
  ring

theorem quadraticResidueAmplitude_norm {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (h₀ s v : ℕ) (r : ZMod q) :
    ‖quadraticResidueAmplitude g a h₀ s v r‖ = ‖g (a * r ^ 2 * (s : ZMod q))‖ := by
  simp only [quadraticResidueAmplitude, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]

theorem sum_by_zmod_residues {q : ℕ} [NeZero q] (W : Finset ℕ) (f : ℕ → ℂ) :
    (∑ w ∈ W, f w) = ∑ r : ZMod q, ∑ w ∈ W.filter (fun w : ℕ => (w : ZMod q) = r), f w := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp

theorem quadraticDensitySum_residue_decomposition {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (W : Finset ℕ) (a : ZMod q) (h₀ s v : ℕ)
    (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) :
    quadraticDensitySum g W a ((h₀ : ℝ) + θ) Φ R v s =
      (Real.sqrt (R * q / ((s : ℝ) * v)) : ℂ)⁻¹ *
        ∑ r : ZMod q, quadraticResidueAmplitude g a h₀ s v r *
          ∑ w ∈ W.filter (fun w : ℕ => (w : ZMod q) = r), quadraticResidueWave (q := q) θ Φ R s v w := by
  rw [quadraticDensitySum, sum_by_zmod_residues (q := q)]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hwr := (Finset.mem_filter.mp hw).2
  rw [quadraticDensityTerm_residue_factor, hwr]

end Ostmann

end OAI
