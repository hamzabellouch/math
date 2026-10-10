import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDensitySum
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSupportCount

namespace OAI

/-! # Exact finite cutoffs for compactly supported quadratic transforms -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def quadraticCompactCutoff (q : ℕ) (R v C : ℝ) (N : ℕ) : Finset ℕ :=
  Finset.Ioc 0 ⌊Real.sqrt (C * R * q / ((N : ℝ) * v))⌋₊

theorem quadraticCompactCutoff_spec (q : ℕ) (R v C : ℝ) (N : ℕ)
    (hR : 0 ≤ R) (hv : 0 ≤ v) (hC : 0 ≤ C) :
    ∀ w ∈ quadraticCompactCutoff q R v C N,
      0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * q / ((N : ℝ) * v) := by
  intro w hw
  obtain ⟨hw0, hw⟩ := Finset.mem_Ioc.mp hw
  refine ⟨hw0, ?_⟩
  have hQ : 0 ≤ C * R * q / ((N : ℝ) * v) := by positivity
  have hle : (w : ℝ) ≤ Real.sqrt (C * R * q / ((N : ℝ) * v)) :=
    (Nat.cast_le.mpr hw).trans (Nat.floor_le (Real.sqrt_nonneg _))
  nlinarith [Real.sq_sqrt hQ, Real.sqrt_nonneg (C * R * q / ((N : ℝ) * v)), (Nat.cast_nonneg w : (0 : ℝ) ≤ w)]

theorem quadraticDensityTerm_mem_cutoff {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R v C : ℝ) (N s w : ℕ) (hR : 0 < R) (hv : 0 < v) (hN : 0 < N)
    (hs : N ≤ s) (hw : 0 < w) (hΦ : ∀ x : ℝ, C < x → Φ x = 0)
    (hne : quadraticDensityTerm g a θ Φ R v s w ≠ 0) :
    w ∈ quadraticCompactCutoff q R v C N := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsR : (N : ℝ) ≤ s := Nat.cast_le.mpr hs
  have hsupport : (s : ℝ) * v * (w : ℝ) ^ 2 / (R * q) ≤ C := by
    by_contra hh
    have hz := hΦ _ (lt_of_not_ge hh)
    exact hne (by simp only [quadraticDensityTerm, hz, mul_zero])
  have hb : (w : ℝ) ^ 2 ≤ C * R * q / ((N : ℝ) * v) := by
    apply (le_div_iff₀ (mul_pos hNR hv)).mpr
    have hh := (div_le_iff₀ (mul_pos hR hq)).mp hsupport
    have hm := mul_le_mul_of_nonneg_right hsR (show 0 ≤ v * (w : ℝ) ^ 2 by positivity)
    nlinarith only [hh, hm]
  exact Finset.mem_Ioc.mpr ⟨hw, Nat.le_floor (Real.le_sqrt_of_sq_le hb)⟩

noncomputable def positiveQuadraticSum {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (s : ℕ) : ℂ :=
  ((Real.sqrt (R * q / ((s : ℝ) * v)) : ℝ) : ℂ)⁻¹ *
    ∑' w : ℕ, if 0 < w then quadraticDensityTerm g a θ Φ R v s w else 0

/-- Compact support makes the positive quadratic series exactly finite,
with one common cutoff for every index in the dyadic segment. -/
theorem positiveQuadraticSum_eq_cutoff {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R v C : ℝ) (N s : ℕ) (hR : 0 < R) (hv : 0 < v) (hN : 0 < N)
    (hs : N ≤ s) (hΦ : ∀ x : ℝ, C < x → Φ x = 0) :
    positiveQuadraticSum g a θ Φ R v s =
      quadraticDensitySum g (quadraticCompactCutoff q R v C N) a θ Φ R v s := by
  classical
  unfold positiveQuadraticSum quadraticDensitySum
  congr 1
  calc
    _ = ∑ w ∈ quadraticCompactCutoff q R v C N,
        if 0 < w then quadraticDensityTerm g a θ Φ R v s w else 0 := by
      apply tsum_eq_sum
      intro w hw
      by_cases hw0 : 0 < w
      · simp only [ite_eq_left hw0]
        by_contra hn
        exact hw (quadraticDensityTerm_mem_cutoff g a θ Φ R v C N s w hR hv hN hs hw0 hΦ hn)
      · simp only [ite_eq_right hw0]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      exact ite_eq_left (Finset.mem_Ioc.mp hw).1

end Ostmann

end OAI
