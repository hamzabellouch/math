import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.EliminationCallBounds
import OAI.Analysis.MatrixSigning.Machines.CommonDenominatorLift
import OAI.Analysis.MatrixSigning.Optimization.TerminalWitnessBounds

namespace OAI

section

namespace KS.W17

open KS.W07

def CommonHeight {n : ℕ} (y : Fin n → ℚ) (E : ℕ) : Prop :=
  ∃ D : ℕ, 0 < D ∧ D ≤ 2 ^ E ∧ ∃ Z : Fin n → ℤ,
    (∀ i, y i = (Z i : ℚ) / D) ∧ ∀ i, (Z i).natAbs ≤ 2 ^ E

theorem CommonHeight.mono {n E F : ℕ} {y : Fin n → ℚ}
    (h : CommonHeight y E) (hEF : E ≤ F) : CommonHeight y F := by
  obtain ⟨D, hD, hDb, Z, hy, hZ⟩ := h
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hEF
  exact ⟨D, hD, hDb.trans hp, Z, hy, fun i => (hZ i).trans hp⟩

theorem CommonHeight.parts_bound {n E : ℕ} {y : Fin n → ℚ}
    (h : CommonHeight y E) (i : Fin n) :
    (y i).num.natAbs ≤ 2 ^ E ∧ (y i).den ≤ 2 ^ E := by
  obtain ⟨D, hD, hDb, Z, hy, hZ⟩ := h
  have hd : (D : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.ne_of_gt hD)
  have he : y i = Rat.divInt (Z i) (D : ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast]
    exact hy i
  rw [he]
  exact ⟨(KS.W30.divInt_num_natAbs_le _ _ hd).trans (hZ i),
    (KS.W30.divInt_den_le _ _ hd).trans (by simpa using hDb)⟩

theorem commonHeight_single {n : ℕ} (i : Fin n) :
    CommonHeight (Pi.single i (1 : ℚ)) 0 := by
  refine ⟨1, by decide, by simp, Pi.single i 1, ?_, ?_⟩
  · intro j
    by_cases hj : j = i <;> simp [hj]
  · intro j
    by_cases hj : j = i <;> simp [hj]

theorem CommonHeight.cons_zero {n E : ℕ} {y : Fin n → ℚ}
    (h : CommonHeight y E) : CommonHeight (Fin.cons 0 y) E := by
  obtain ⟨D, hD, hDb, Z, hy, hZ⟩ := h
  refine ⟨D, hD, hDb, Fin.cons 0 Z, ?_, ?_⟩
  · intro i
    exact Fin.cases (by simp) (fun j => by simpa using hy j) i
  · intro i
    exact Fin.cases (by simp) (fun j => by simpa using hZ j) i

theorem schurWitnessLift_eq_prependLinear {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (y : Fin n → ℚ) :
    schurWitnessLift M y =
      KS.W30.prependLinear (fun j => -(M 0 j.succ / M 0 0)) y := by
  unfold schurWitnessLift KS.W30.prependLinear
  apply congrArg (fun z : ℚ => (Fin.cons z y : Fin (n + 1) → ℚ))
  calc
    -(∑ j, M 0 j.succ * y j) / M 0 0 =
        ∑ j, -(M 0 j.succ * y j) / M 0 0 := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_neg_distrib, Finset.sum_mul]
    _ = ∑ j, -(M 0 j.succ / M 0 0) * y j := by
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem DenseEliminationCall.lift_coefficient_parts {N t : ℕ}
    {A : DenseRatMatrix N} {S : DenseRatMatrix (t + 1)}
    (h : DenseEliminationCall A S) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2 ^ b) (j : Fin t) :
    let c := -(DenseRatMatrix.decode S 0 j.succ / DenseRatMatrix.decode S 0 0)
    c.num.natAbs ≤ 2 ^ (2 * KS.W30.inverseBitBound N b) ∧
      c.den ≤ 2 ^ (2 * KS.W30.inverseBitBound N b) := by
  have hp := h.entry_parts_size_le b hnum hden 0 0
  have hr := h.entry_parts_size_le b hnum hden 0 j.succ
  have hd := KS.W30.div_parts_le_two_pow _ _
    (KS.W30.inverseBitBound N b) (KS.W30.inverseBitBound N b)
    (Nat.le_of_lt (Nat.size_le.mp hr.1)) (Nat.le_of_lt (Nat.size_le.mp hr.2))
    (Nat.le_of_lt (Nat.size_le.mp hp.1)) (Nat.le_of_lt (Nat.size_le.mp hp.2))
  simpa [Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, Int.natAbs_neg, two_mul] using hd

theorem CommonHeight.schurWitnessLift {n E H : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) {y : Fin n → ℚ}
    (hy : CommonHeight y E)
    (hcnum : ∀ j : Fin n, (-(M 0 j.succ / M 0 0)).num.natAbs ≤ 2 ^ H)
    (hcden : ∀ j : Fin n, (-(M 0 j.succ / M 0 0)).den ≤ 2 ^ H) :
    CommonHeight (schurWitnessLift M y) (E + (n + 1) * H + n + 1) := by
  obtain ⟨D, hD, hDb, Z, hy, hZ⟩ := hy
  rw [schurWitnessLift_eq_prependLinear]
  exact KS.W30.prependLinear_common_height _ y H E hcnum hcden D hD hDb Z hy hZ

def witnessHeightBudget (N b t : ℕ) : ℕ :=
  (t + 1) * ((N + 2) * (3 * KS.W30.inverseBitBound N b + 4))

theorem DenseEliminationCall.dimension_le {N t : ℕ} {A : DenseRatMatrix N}
    {S : DenseRatMatrix t} (h : DenseEliminationCall A S) : t ≤ N := by
  obtain ⟨k, p, r, hp⟩ := h.pivotTrace
  have hs := hp.size_bound
  omega

theorem denseNegativeWitness_commonHeight {N t : ℕ} (A : DenseRatMatrix N)
    (b : ℕ) (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2 ^ b)
    (S : DenseRatMatrix t) (hcall : DenseEliminationCall A S)
    (y : Vector ℚ t) (hout : denseNegativeWitness t S = some y) :
    CommonHeight (decodeRatVector y) (witnessHeightBudget N b t) := by
  let H := KS.W30.inverseBitBound N b
  let K := (N + 2) * (3 * H + 4)
  have hK : 3 * H + 3 ≤ K := by dsimp [K]; nlinarith
  change CommonHeight (decodeRatVector y) ((t + 1) * K)
  induction t with
  | zero => simp [denseNegativeWitness] at hout
  | succ t ih =>
      let M := DenseRatMatrix.decode S
      have hentry : ∀ i j, (M i j).num.natAbs ≤ 2 ^ H ∧ (M i j).den ≤ 2 ^ H := by
        intro i j
        have hb := hcall.entry_parts_size_le b hnum hden i j
        exact ⟨Nat.le_of_lt (Nat.size_le.mp hb.1), Nat.le_of_lt (Nat.size_le.mp hb.2)⟩
      by_cases hn : M 0 0 < 0
      · have he : y = Vector.ofFn (Pi.single 0 (1 : ℚ)) := by
          simpa [denseNegativeWitness, M, hn] using hout.symm
        subst y
        simpa using (commonHeight_single (0 : Fin (t + 1))).mono (Nat.zero_le ((t + 2) * K))
      · by_cases hz : M 0 0 = 0
        · cases hf : firstNonzeroOffDiagonal M with
          | some j =>
              have he : y = Vector.ofFn (zeroPivotWitness M 0 j.succ) := by
                simpa [denseNegativeWitness, M, hn, hz, hf] using hout.symm
              subst y
              have hq := hentry j.succ j.succ
              have hr := hentry 0 j.succ
              have hc : CommonHeight (zeroPivotWitness M 0 j.succ) (3 * H + 3) := by
                exact KS.W30.zeroPivot_pair_common_height 0 j.succ (Fin.succ_ne_zero j).symm
                  (M j.succ j.succ) (M 0 j.succ) H hq.1 hq.2 hr.1 hr.2
              simpa using hc.mono (show 3 * H + 3 ≤ (t + 2) * K by nlinarith)
          | none =>
              let T := DenseRatMatrix.ofMatrix (trailingMatrix M)
              have ht : DenseEliminationCall A T := DenseEliminationCall.zero hcall hz hf
              rw [denseNegativeWitness_zero_recurse S hz hf] at hout
              change (denseNegativeWitness t T).map
                (fun z => Vector.ofFn (Fin.cons 0 (decodeRatVector z))) = some y at hout
              cases ho : denseNegativeWitness t T with
              | none => simp [ho] at hout
              | some z =>
                  have he : y = Vector.ofFn (Fin.cons 0 (decodeRatVector z)) := by
                    simpa [ho] using hout.symm
                  subst y
                  have hc := (ih T ht z ho).cons_zero
                  simpa using hc.mono (show (t + 1) * K ≤ (t + 2) * K by nlinarith)
        · have hp : 0 < M 0 0 := lt_of_le_of_ne (not_lt.mp hn) (Ne.symm hz)
          let T := DenseRatMatrix.ofMatrix (schurTail M)
          have ht : DenseEliminationCall A T := DenseEliminationCall.positive hcall hp
          rw [denseNegativeWitness_positive_recurse S hp] at hout
          change (denseNegativeWitness t T).map
            (fun z => Vector.ofFn (schurWitnessLift M (decodeRatVector z))) = some y at hout
          cases ho : denseNegativeWitness t T with
          | none => simp [ho] at hout
          | some z =>
              have he : y = Vector.ofFn (schurWitnessLift M (decodeRatVector z)) := by
                simpa [ho] using hout.symm
              subst y
              have hc := CommonHeight.schurWitnessLift M (ih T ht z ho)
                (fun j => (hcall.lift_coefficient_parts b hnum hden j).1)
                (fun j => (hcall.lift_coefficient_parts b hnum hden j).2)
              have hdim := hcall.dimension_le
              have hinc : (t + 1) * (2 * H) + t + 1 ≤ K := by
                have hmul := Nat.mul_le_mul (show t + 1 ≤ N + 2 by omega)
                  (show 2 * H + 1 ≤ 3 * H + 4 by omega)
                dsimp [K]
                nlinarith
              simpa [H] using hc.mono
                (show (t + 1) * K + (t + 1) * (2 * H) + t + 1 ≤ (t + 2) * K by nlinarith)

theorem denseNegativeWitness_output_parts {N : ℕ} (A : DenseRatMatrix N)
    (b : ℕ) (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2 ^ b)
    (y : Vector ℚ N) (hout : denseNegativeWitness N A = some y) (i : Fin N) :
    Nat.size (decodeRatVector y i).num.natAbs ≤ witnessHeightBudget N b N + 1 ∧
      Nat.size (decodeRatVector y i).den ≤ witnessHeightBudget N b N + 1 := by
  have h := (denseNegativeWitness_commonHeight A b hnum hden A
    DenseEliminationCall.initial y hout).parts_bound i
  have hp : 2 ^ witnessHeightBudget N b N < 2 ^ (witnessHeightBudget N b N + 1) := by
    rw [pow_succ]
    have hpos : 0 < 2 ^ witnessHeightBudget N b N := pow_pos (by decide) _
    omega
  exact ⟨Nat.size_le.mpr (h.1.trans_lt hp), Nat.size_le.mpr (h.2.trans_lt hp)⟩

end KS.W17

end

end OAI
