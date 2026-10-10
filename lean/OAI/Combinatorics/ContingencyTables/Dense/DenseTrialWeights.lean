import OAI.Combinatorics.ContingencyTables.Dense.DenseTrial

namespace OAI

/-! # Equal weight of all accepted dense trials

The bin is sampled with its stationary weight, and the integral offset
uniformly. The unique trial producing any given table lies in a bin of
weight one. Conditioning this finite law on acceptance is therefore
exactly uniform on the actual tables.
-/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]
variable {q : ℕ}

def trialReal (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) : Fin q → ℝ :=
  fun j => (trialFree R P d e t (e.symm j) : ℝ) / (integerWidth R P d (e.symm j) : ℝ)

omit [Fintype I] [Fintype J] in
theorem trialReal_closed (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) :
    ClosedBin (corner t.1) (trialReal R P d e t) := by
  intro j
  have hw : (0 : ℝ) < integerWidth R P d (e.symm j) := by
    exact_mod_cast integerWidth_pos R P d hd hR hP (e.symm j)
  have ho : (0 : ℝ) ≤ (t.2 (e.symm j)).val := Nat.cast_nonneg _
  have ho' : ((t.2 (e.symm j)).val : ℝ) < integerWidth R P d (e.symm j) := by
    exact_mod_cast (t.2 (e.symm j)).isLt
  have hc : (((corner t.1 j).toNat : ℕ) : ℝ) = (corner t.1 j : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (t.1 j).property.1
  have hz : (trialFree R P d e t (e.symm j) : ℝ) =
      (t.2 (e.symm j)).val + (integerWidth R P d (e.symm j) : ℝ) * (corner t.1 j : ℝ) := by
    change ((trialBoxEquiv e (integerWidth R P d) (4 * d ^ 8) (t.1, t.2) (e.symm j)).val : ℝ) = _
    rw [trialBoxEquiv_val, Equiv.apply_symm_apply, Nat.cast_add, Nat.cast_mul, hc]
  change (corner t.1 j : ℝ) ≤ _ / _ ∧ _ / _ ≤ (corner t.1 j : ℝ) + 1
  constructor
  · apply (le_div_iff₀ hw).mpr
    rw [hz]
    nlinarith
  · apply (div_le_iff₀ hw).mpr
    rw [hz]
    nlinarith

theorem trialReal_feasible_iff (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) :
    denseGridFeasible R P d e (trialReal R P d e t) ↔ TrialAccepted R P d e t := by
  have h := DenseAffine.integer_acceptance_iff R P
    (fun i j => integerWidth R P d (i, j))
    (fun i j => integerWidth_pos R P d hd hR hP (i, j)) (trialFree R P d e t)
  change (∀ i j, 0 ≤ DenseAffine.table (fun i => (R i : ℝ)) (fun j => (P j : ℝ))
    (fun i j => (integerWidth R P d (i, j) : ℝ))
      (fun p => trialReal R P d e t (e p)) i j) ↔ _
  simpa only [trialReal, Equiv.symm_apply_apply, TrialAccepted] using h

variable [DecidableEq I] [DecidableEq J]

theorem acceptedTrial_binWeight_one (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (t : DenseTrial R P d q) (ht : TrialAccepted R P d e t) :
    denseBinWeight R P d e t.1 = 1 :=
  denseBinWeight_eq_one R P d hd hR hP hRmax hPmax hfree e t.1
    (trialReal R P d e t) (trialReal_closed R P d hd hR hP e t)
    ((trialReal_feasible_iff R P d hd hR hP e t).mpr ht)

def denseTrialMass (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) : ℝ :=
  denseBinWeight R P d e t.1 /
    (∑ a : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e a) /
      Fintype.card (Offset (integerWidth R P d))

theorem denseTrialMass_pos (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) :
    0 < denseTrialMass R P d e t := by
  let : Nonempty (Grid (I := Fin q) (4 * d ^ 8)) := ⟨t.1⟩
  let : Nonempty (Offset (integerWidth R P d)) :=
    ⟨fun p => ⟨0, integerWidth_pos R P d hd hR hP p⟩⟩
  have hZ : 0 < ∑ a : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e a :=
    Finset.sum_pos (fun _ _ => DenseWeights.binWeight_pos _ _ _) Finset.univ_nonempty
  have hO : (0 : ℝ) < Fintype.card (Offset (integerWidth R P d)) := by
    exact_mod_cast Fintype.card_pos (α := Offset (integerWidth R P d))
  exact div_pos (div_pos (DenseWeights.binWeight_pos _ _ _) hZ) hO

theorem denseTrialMass_sum (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) :
    ∑ t : DenseTrial R P d q, denseTrialMass R P d e t = 1 := by
  let : Nonempty (Grid (I := Fin q) (4 * d ^ 8)) :=
    ⟨fun _ => ⟨0, by have h := denseGridSize_pos d hd; constructor <;> omega⟩⟩
  let : Nonempty (Offset (integerWidth R P d)) :=
    ⟨fun p => ⟨0, integerWidth_pos R P d hd hR hP p⟩⟩
  have hZ : (∑ a : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e a) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun _ _ => DenseWeights.binWeight_pos _ _ _) Finset.univ_nonempty)
  have hO : (Fintype.card (Offset (integerWidth R P d)) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Fintype.card_pos (α := Offset (integerWidth R P d)))
  rw [Fintype.sum_prod_type]
  simp only [denseTrialMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp_rw [mul_div_cancel₀ _ hO]
  rw [← Finset.sum_div, div_self hZ]

/-- Conditioning the actual stationary-bin/uniform-offset trial law on
acceptance assigns each table exactly the reciprocal of the table count. -/
theorem denseTrial_conditional_uniform (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q) (X : Table R P) :
    denseTrialMass R P d e (tableTrial R P d hd hR hP e X) /
      (∑ Y : Table R P, denseTrialMass R P d e (tableTrial R P d hd hR hP e Y)) =
        1 / Fintype.card (Table R P) := by
  have heq (Y : Table R P) : denseTrialMass R P d e (tableTrial R P d hd hR hP e Y) =
      1 / (∑ a : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e a) /
        Fintype.card (Offset (integerWidth R P d)) := by
    unfold denseTrialMass
    rw [acceptedTrial_binWeight_one R P d hd hR hP hRmax hPmax hfree e _
      (tableTrial_accepted R P d hd hR hP e Y)]
  have ha := denseTrialMass_pos R P d hd hR hP e (tableTrial R P d hd hR hP e X)
  rw [heq X] at ha
  simp_rw [heq]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_comm (Fintype.card (Table R P) : ℝ)]
  simpa only [one_div] using div_mul_cancel_left₀ (ne_of_gt ha) (Fintype.card (Table R P) : ℝ)

end

end ContingencyTables.GridBoundary

end OAI
