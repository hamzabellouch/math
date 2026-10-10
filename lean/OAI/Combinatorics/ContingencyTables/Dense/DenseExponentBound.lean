import OAI.Combinatorics.ContingencyTables.Transport.DyadicAcceptance

namespace OAI

/-! # Bounded bit allowance for every dense Metropolis decision -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

theorem denseExponent_upper (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4 * d ^ 8)) :
    denseExponent R P d e a ≤ 4 * d ^ 5 := by
  have hcube (p : I × J) : 0 ≤ realCorner a (e p) ∧ realCorner a (e p) ≤ 4 * (d : ℝ) ^ 8 := by
    have hlo : (0 : ℤ) ≤ corner a (e p) := (a (e p)).property.1
    have hhi : corner a (e p) ≤ (4 * d ^ 8 : ℕ) := by
      have h : corner a (e p) ≤ (4 * d ^ 8 : ℕ) - 1 := (a (e p)).property.2
      omega
    constructor
    · change (0 : ℝ) ≤ (corner a (e p) : ℝ)
      exact_mod_cast hlo
    · change (corner a (e p) : ℝ) ≤ 4 * (d : ℝ) ^ 8
      exact_mod_cast hhi
  have hp := (DenseAffine.densePenalty_cube_bound R P d hd hR hP hRmax hPmax
    hdimR hdimP hfree htotal _ hcube).2
  have he : (denseExponent R P d e a : ℝ) =
      (⌊(d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a)⌋ : ℤ) := by
    exact_mod_cast denseExponent_eq_floor R P d e a
  have hf := Int.floor_le ((d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a))
  have hmul := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ (d : ℝ) ^ 4 by positivity)
  change (d : ℝ) ^ 4 * denseGridPenalty R P d e (realCorner a) ≤ (d : ℝ) ^ 4 * (4 * d) at hmul
  have hbound : (denseExponent R P d e a : ℝ) ≤ 4 * (d : ℝ) ^ 5 := by
    rw [he]
    nlinarith
  exact_mod_cast hbound

/-- The paper's fixed allowance implements every possible acceptance
probability exactly, including a proposed move whose probability is one. -/
theorem denseMetropolis_finite_coin (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) (a b : Grid (I := Fin q) (4 * d ^ 8)) :
    ((Finset.univ.filter (FairBits.acceptDyadic
      (denseExponent R P d e b - denseExponent R P d e a) (8 * d ^ 5))).card : ℝ) /
        (2 : ℝ) ^ (8 * d ^ 5) =
      min 1 (denseBinWeight R P d e b / denseBinWeight R P d e a) := by
  rw [FairBits.acceptDyadic_probability]
  · exact (dense_acceptance_dyadic R P d e a b).symm
  · exact (Nat.sub_le _ _).trans ((denseExponent_upper R P d hd hR hP hRmax hPmax
      hdimR hdimP hfree htotal e b).trans (by omega))

end ContingencyTables.GridBoundary

end OAI
