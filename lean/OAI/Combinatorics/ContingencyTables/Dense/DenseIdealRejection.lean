import OAI.Combinatorics.ContingencyTables.Dense.DenseRationalTrial
import OAI.Combinatorics.ContingencyTables.Dense.DenseErrorArithmetic

namespace OAI

/-! # Bounded rejection of independent actual ideal dense trials -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

/-- The finite first-success law uses the actual per-table trial masses.
The sole bias after ideal trials comes from the feasible fallback. -/
theorem dense_ideal_rejection_variation (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (J₀ : ℕ) (fallback : Table R P) :
    let g := rationalTableMass R P d hd hR hP e
    (((∑ X : Table R P,
      |outputMass g (1 - ∑ Y, g Y) J₀ fallback X - uniformMass (α := Table R P)|) / 2 : ℚ) : ℝ) ≤
        (63 / 64 : ℝ) ^ J₀ := by
  let : Nonempty (Table R P) := ⟨fallback⟩
  let g := rationalTableMass R P d hd hR hP e
  let s : ℚ := ∑ X, g X
  have hcast : (s : ℝ) = denseAcceptanceMass R P d e := by
    dsimp [s, g]
    rw [Rat.cast_sum]
    exact rationalTableMass_total R P d hd hR hP e htotal
  have hs : (1 / 32 : ℚ) ≤ s := by
    have h := denseAcceptanceMass_lower R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e
    rw [← hcast] at h
    have hc : ((1 / 32 : ℚ) : ℝ) ≤ (s : ℝ) := by norm_num; exact h
    exact_mod_cast hc
  have hs1 : s ≤ 1 := by
    have h := denseAcceptanceMass_le_one R P d hd hR hP e
    rw [← hcast] at h
    exact_mod_cast h
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hg : g = fun _ => s * uniformMass (α := Table R P) := by
    funext X
    have h := rationalTableMass_uniform R P d hd hR hP hRmax hPmax hfree e X
    change g X / s = uniformMass (α := Table R P) at h
    simpa only [mul_comm] using (div_eq_iff (ne_of_gt hs0)).mp h
  have hv := stationary_variation s hs0.le hs1 J₀ fallback
  rw [← hg] at hv
  have hv' : (((∑ X : Table R P,
      |outputMass g (1 - s) J₀ fallback X - uniformMass (α := Table R P)|) / 2 : ℚ) : ℝ) ≤
        ((1 - s : ℚ) : ℝ) ^ J₀ := by exact_mod_cast hv
  apply hv'.trans
  apply pow_le_pow_left₀
  · exact_mod_cast sub_nonneg.mpr hs1
  · have h : (1 - s : ℚ) ≤ 63 / 64 := by linarith
    have hc : ((1 - s : ℚ) : ℝ) ≤ ((63 / 64 : ℚ) : ℝ) := by exact_mod_cast h
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc

/-- With the manuscript's actual trial count, the ideal fallback error
already consumes at most one quarter of the requested error budget. -/
theorem dense_ideal_rejection_schedule (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (h : ℕ) (fallback : Table R P) :
    let g := rationalTableMass R P d hd hR hP e
    (((∑ X : Table R P,
      |outputMass g (1 - ∑ Y, g Y) (d ^ 4 * (h + 1)) fallback X -
        uniformMass (α := Table R P)|) / 2 : ℚ) : ℝ) ≤ (2 : ℝ) ^ (-(h : ℝ) - 2) :=
  (dense_ideal_rejection_variation R P d hd hR hP hRmax hPmax hdimR hdimP hfree htotal e _ fallback).trans
    (dense_failure_error_budget d h hd)

end

end ContingencyTables.GridBoundary

end OAI
