import OAI.NumberTheory.Ostmann.Construction.WordTransferGuardBounds

namespace OAI

/-! # One residue gate and one polynomial partition for a complete guard family -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def wordGuardNumerators {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ) :
    Fin (k + k) → MvPolynomial σ ℤ :=
  Fin.append (fun i => (G i).pivot.cleared.numerator) (fun i => (G i).rightProduct.cleared.numerator)

noncomputable def wordGuardDenominators {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ) :
    Fin (k + k) → ℤ :=
  Fin.append (fun i => (G i).pivot.cleared.denominator) (fun i => (G i).rightProduct.cleared.denominator)

def wordGuardModuli {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ) : Fin (k + k) → ℕ :=
  Fin.append (fun i => (G i).right.natAbs) (fun i => (G i).root.natAbs)

noncomputable def wordGuardPolynomials {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ)
    (a : σ → ℤ) (coord : σ) : Fin (k + (k + k)) → Polynomial ℝ :=
  Fin.append (fun i => (G i).polynomials a coord 0)
    (Fin.append (fun i => (G i).polynomials a coord 1) (fun i => (G i).polynomials a coord 2))

noncomputable def wordGuardKeep {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ)
    (code : Fin (k + (k + k)) → Bool) : Bool :=
  decide (∀ i, (G i).frequencyBounds) && decide (∀ j, code j = true)

theorem wordGuard_residue_iff {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ) (x : σ → ℤ) :
    (∀ j, smallDivisionTest (MvPolynomial.eval₂ (RingHom.id ℤ) x (wordGuardNumerators G j))
      (wordGuardDenominators G j) (wordGuardModuli G j)) ↔ ∀ i, (G i).residueAt x := by
  simp only [wordGuardNumerators, wordGuardDenominators, wordGuardModuli,
    Fin.forall_fin_add, Fin.append_left, Fin.append_right, WordTransferGuard.residueAt,
    MvPolynomial.coe_eval₂Hom, forall_and]

theorem wordGuard_keep_iff {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ)
    (a : σ → ℤ) (coord : σ) (z : ℝ) :
    wordGuardKeep G (polynomialSupportCode (wordGuardPolynomials G a coord) z) = true ↔
      (∀ i, (G i).frequencyBounds) ∧ ∀ i j, 0 ≤ ((G i).polynomials a coord j).eval z := by
  simp only [wordGuardKeep, Bool.and_eq_true, decide_eq_true_eq, polynomialSupportCode,
    wordGuardPolynomials, Fin.forall_fin_add, Fin.append_left, Fin.append_right]
  constructor
  · rintro ⟨hf, h0, h1, h2⟩
    refine ⟨hf, fun i j => ?_⟩
    fin_cases j
    · exact h0 i
    · exact h1 i
    · exact h2 i
  · rintro ⟨hf, hp⟩
    exact ⟨hf, (fun i => hp i 0), (fun i => hp i 1), (fun i => hp i 2)⟩

/-- The full branching support is exactly the residue-and-polynomial gate
accepted by the one-sided estimate. -/
theorem wordGuard_family_support {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ)
    (a : σ → ℤ) (coord : σ) (z : ℤ) :
    (∀ i, (G i).ValidAt (Function.update a coord z)) ↔
      (∀ j, smallDivisionTest
        (MvPolynomial.eval₂ (RingHom.id ℤ) (Function.update a coord z) (wordGuardNumerators G j))
        (wordGuardDenominators G j) (wordGuardModuli G j)) ∧
      wordGuardKeep G (polynomialSupportCode (wordGuardPolynomials G a coord) (z : ℝ)) = true := by
  rw [wordGuard_residue_iff, wordGuard_keep_iff]
  simp only [WordTransferGuard.validAt_polynomials, forall_and]

theorem wordGuard_family_amplitude {σ : Type*} {k n : ℕ} (G : Fin k → WordTransferGuard σ)
    (a : σ → ℤ) (coord : σ) (F : Fin n → ClippedPolynomialFactor) (z : ℤ) :
    guardedHistoryAmplitude (wordGuardNumerators G) (wordGuardDenominators G) (wordGuardModuli G)
      a coord F (wordGuardPolynomials G a coord) (wordGuardKeep G) z =
      (if ∀ i, (G i).ValidAt (Function.update a coord z) then 1 else 0) *
        smoothPolynomialWeight F (z : ℝ) := by
  simp only [wordGuard_family_support]
  unfold guardedHistoryAmplitude polynomialAmplitude
  split_ifs <;> simp_all

theorem wordGuard_family_degree {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ)
    (a : σ → ℤ) (coord : σ) :
    (∑ j, (wordGuardPolynomials G a coord j).natDegree) ≤
      3 * ∑ i, max (G i).pivot.cost (G i).rightProduct.cost := by
  simp only [wordGuardPolynomials, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have h0 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
    (G i).polynomials_degree a coord 0)
  have h1 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
    (G i).polynomials_degree a coord 1)
  have h2 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
    (G i).polynomials_degree a coord 2)
  omega

end Ostmann

end OAI
