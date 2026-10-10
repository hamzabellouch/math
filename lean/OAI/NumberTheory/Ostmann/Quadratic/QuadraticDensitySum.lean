import OAI.NumberTheory.Ostmann.QuadraticCenter.TruncatedQuadraticCorrelation

namespace OAI

/-! # The manuscript's finite quadratic sums and their zero nonunit terms -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def quadraticDensityTerm {q : ℕ} [NeZero q] (g : ZMod q → ℂ)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (s w : ℕ) : ℂ :=
  g (a * (w : ZMod q) ^ 2 * (s : ZMod q)) *
    realAdditivePhase (θ * v * (w : ℝ) ^ 2 / q) ^ s *
      Φ ((s : ℝ) * v * (w : ℝ) ^ 2 / (R * q))

noncomputable def quadraticDensitySum {q : ℕ} [NeZero q] (g : ZMod q → ℂ)
    (W : Finset ℕ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (s : ℕ) : ℂ :=
  ((Real.sqrt (R * q / ((s : ℝ) * v)) : ℝ) : ℂ)⁻¹ *
    ∑ w ∈ W, quadraticDensityTerm g a θ Φ R v s w

noncomputable def unitQuadraticSupport {q : ℕ} (W : Finset ℕ) (a : ZMod q) : Finset ℕ :=
  by
    classical
    exact W.filter (fun w => IsUnit (a * (w : ZMod q) ^ 2))

noncomputable def quadraticUnitScalar {q : ℕ} (a : ZMod q) (w : ℕ) : (ZMod q)ˣ :=
  by
    classical
    exact if h : IsUnit (a * (w : ZMod q) ^ 2) then h.unit else 1

@[simp] theorem mem_unitQuadraticSupport {q : ℕ} (W : Finset ℕ) (a : ZMod q) (w : ℕ) :
    w ∈ unitQuadraticSupport W a ↔ w ∈ W ∧ IsUnit (a * (w : ZMod q) ^ 2) := by
  classical
  exact Finset.mem_filter

theorem unitQuadraticSupport_subset {q : ℕ} (W : Finset ℕ) (a : ZMod q) :
    unitQuadraticSupport W a ⊆ W := by
  intro w hw
  exact (mem_unitQuadraticSupport W a w).mp hw |>.1

theorem quadraticDensityTerm_nonunit {q : ℕ} [NeZero q] (g : ZMod q → ℂ)
    (hg : ∀ x, ¬IsUnit x → g x = 0) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R v : ℝ) (s w : ℕ) (hw : ¬IsUnit (a * (w : ZMod q) ^ 2)) :
    quadraticDensityTerm g a θ Φ R v s w = 0 := by
  have hn : ¬IsUnit (a * (w : ZMod q) ^ 2 * (s : ZMod q)) :=
    fun h => hw (isUnit_of_mul_isUnit_left h)
  simp only [quadraticDensityTerm, hg _ hn, zero_mul]

theorem quadraticDensityTerm_eq_wave {q : ℕ} [NeZero q] (g : ZMod q → ℂ)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (s w : ℕ)
    (hw : IsUnit (a * (w : ZMod q) ^ 2)) (hw0 : 0 < w) (hR : 0 < R) (hv : 0 < v) :
    quadraticDensityTerm g a θ Φ R v s w =
      densityWave g (quadraticUnitScalar a w) Φ
        (θ * v * (w : ℝ) ^ 2 / q) (R * q / (v * (w : ℝ) ^ 2)) s := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw0
  have hy : (s : ℝ) / (R * q / (v * (w : ℝ) ^ 2)) =
      (s : ℝ) * v * (w : ℝ) ^ 2 / (R * q) := by field_simp
  simp only [quadraticDensityTerm, densityWave, quadraticUnitScalar, dite_eq_left hw,
    IsUnit.unit_spec, hy]
  ring

/-- Removing the zero nonunit terms leaves precisely the unit-wave sum to
which the original-density correlation estimate applies. -/
theorem quadraticDensitySum_eq_unit_waves {q : ℕ} [NeZero q] (g : ZMod q → ℂ)
    (hg : ∀ x, ¬IsUnit x → g x = 0) (W : Finset ℕ)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (s : ℕ)
    (hW : ∀ w ∈ W, 0 < w) (hR : 0 < R) (hv : 0 < v) :
    quadraticDensitySum g W a θ Φ R v s =
      normalizedDensityWaveSum g (unitQuadraticSupport W a) (quadraticUnitScalar a) Φ
        (fun w => θ * v * (w : ℝ) ^ 2 / q) (fun w => R * q / (v * (w : ℝ) ^ 2)) R v s := by
  classical
  unfold quadraticDensitySum normalizedDensityWaveSum
  congr 1
  calc
    _ = ∑ w ∈ unitQuadraticSupport W a, quadraticDensityTerm g a θ Φ R v s w := by
      symm
      apply Finset.sum_subset (unitQuadraticSupport_subset W a)
      intro w hw hn
      have hnu : ¬IsUnit (a * (w : ZMod q) ^ 2) := by
        intro hu
        exact hn ((mem_unitQuadraticSupport W a w).mpr ⟨hw, hu⟩)
      exact quadraticDensityTerm_nonunit g hg a θ Φ R v s w hnu
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      obtain ⟨hw, hu⟩ := (mem_unitQuadraticSupport W a w).mp hw
      exact quadraticDensityTerm_eq_wave g a θ Φ R v s w hu (hW w hw) hR hv

end Ostmann

end OAI
