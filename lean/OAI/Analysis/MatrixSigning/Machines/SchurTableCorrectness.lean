import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SchurRowLoop

namespace OAI

section

namespace KS.W07.SchurTableMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open SchurLoopState

def initializeTicks (n : ℕ) : ℕ := SchurDimension.predecessorTicks n +
  ((4*n+6*(Computability.encodeNat n).length+4)+1)

theorem initialize_spec {n : ℕ} (M : DenseRatMatrix (n+1)) :
    RunSpec «initialize» (inputState M) (rowState M 0 n) (initializeTicks n) := by
  let s := inputState M
  let d := Function.update s 30 (Computability.encodeNat n)
  let u := Function.update d 24 (List.replicate n true)
  have hd := SchurDimension.predecessor_spec s n rfl rfl rfl rfl rfl rfl
  have hu := SchurDimension.unary_spec false d n rfl rfl rfl rfl rfl
  have hp := SchurCounters.push_spec (27 : Fin 32) true u
  have hone : Computability.encodeNat 1 = [true] := by decide
  have hout : Function.update u 27 (true::u 27) = rowState M 0 n := by
    funext k; fin_cases k <;> simp [u,d,s,inputState,rowState,hone]
  rw [hout] at hp
  exact hd.compose (hu.compose hp)

theorem initializeTicks_le (n : ℕ) : initializeTicks n ≤ 30*(n+2) := by
  have ln : (Computability.encodeNat n).length ≤ n := by
    change KS.W01.natPayloadLength n ≤ n
    rw [KS.W01.natPayloadLength_eq_size]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have ld : (Computability.encodeNat (n+1)).length ≤ n+1 := by
    change KS.W01.natPayloadLength (n+1) ≤ n+1
    rw [KS.W01.natPayloadLength_eq_size]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  unfold initializeTicks SchurDimension.predecessorTicks
  omega

def finishTicks {n : ℕ} (M : DenseRatMatrix (n+1)) : ℕ :=
  ((Computability.encodeNat (n+1)).length+1) +
    (3*(KS.W08.denseMatrixTape (tailMatrix M)).length+3)

theorem finish_spec {n : ℕ} (M : DenseRatMatrix (n+1)) :
    RunSpec finish (rowState M n 0) (outputState M) (finishTicks M) := by
  let mid := Function.update (rowState M n 0) 27 []
  have hc := KS.W15.RationalMultiply.clear_spec (27 : Fin 32) (rowState M n 0)
  have hclearState : KS.W15.RationalMultiply.clearAfter 27 (rowState M n 0) = mid := by
    funext k
    by_cases hk : k=27 <;> simp [KS.W15.RationalMultiply.clearAfter,mid,hk]
  rw [hclearState] at hc
  have hr := SchurEntryMachine.finish_spec mid (KS.W08.denseMatrixTape (tailMatrix M))
    (by simp [mid,rowState,prefix_complete]) rfl rfl
  have hout : Function.update mid 23 (KS.W08.denseMatrixTape (tailMatrix M)) = outputState M := by
    funext k; fin_cases k <;> simp [mid,rowState,outputState,tailMatrix]
  rw [hout] at hr
  exact hc.compose hr

def totalTicks (n B : ℕ) : ℕ := 30*(n+2) +
  ((n*(rowBudget n B+1)+1) + (n+5+3*(n*n*(32*B+39))))

theorem finishTicks_le {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B) :
    finishTicks M ≤ n+5+3*(n*n*(32*B+39)) := by
  have hp := SchurTable.entry_parts_le M B hnum hden
  have ht := KS.W08.denseMatrixTape_length_le (tailMatrix M) (4*B+3)
    (fun i j => by simpa [tailMatrix] using (hp i j).1)
    (fun i j => by simpa [tailMatrix] using (hp i j).2)
  have ld : (Computability.encodeNat (n+1)).length ≤ n+1 := by
    change KS.W01.natPayloadLength (n+1) ≤ n+1
    rw [KS.W01.natPayloadLength_eq_size]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hexp : 8*(4*B+3)+15 = 32*B+39 := by omega
  rw [hexp] at ht
  unfold finishTicks
  omega

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B) :
    RunSpec program (inputState M) (outputState M) (totalTicks n B) := by
  exact ((initialize_spec M).mono (initializeTicks_le n)).compose
    ((rows_spec M B hnum hden).compose ((finish_spec M).mono (finishTicks_le M B hnum hden)))

theorem run_full {n : ℕ} (M : DenseRatMatrix (n+1)) (B : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (bits : List Bool) (hlen : totalTicks n B ≤ bits.length) :
    program.toMachine.run ⟨some program.initial,inputState M⟩ bits = ⟨none,outputState M⟩ :=
  (full_spec M B hnum hden).run_of_le bits hlen

theorem transient_stack_length {n : ℕ} (M : DenseRatMatrix (n+1))
    (bits : List Bool) (j : Fin 32) :
    (((program.toMachine.run ⟨some program.initial,inputState M⟩ bits).«stacks» j).length) ≤
      (KS.W08.denseMatrixTape M).length + (Computability.encodeNat (n+1)).length + bits.length := by
  have h := program.toMachine.run_stack_length_le
    (⟨some program.initial,inputState M⟩ : Config 32 program.states) bits j
  have hi : (inputState M j).length ≤
      (KS.W08.denseMatrixTape M).length + (Computability.encodeNat (n+1)).length := by
    fin_cases j <;> simp [inputState]
  exact h.trans (Nat.add_le_add_right hi _)

end KS.W07.SchurTableMachine

end

end OAI
