import OAI.Computability.DepthThree.TapeHashClean
import OAI.Computability.DepthThree.TapeHorner
import OAI.Computability.DepthThree.TapeOutput
import OAI.Computability.DepthThree.LanguageInputBlockWords

namespace OAI

namespace DepthThreeLowerBound
namespace TapeEvaluation

open TapeMultiProgram TapeRouting TapeRegister

structure Prepared (σ : TapeStore) (w : List Bool) : Prop where
  workspace : TapeHornerMultiply.Workspace σ (decodeInput w).ringDegree
  clean : TapeHornerPrepare.Clean σ
  data_length : σ dataLength = List.replicate (decodeInput w).dataSize true
  coefficient_count : σ coeffCount = List.replicate (decodeInput w).coefficientCount true
  data_bits : σ dataBits = inputBlockData w .data
  key_bits : σ keyBits = inputBlockData w .hash
  polynomial_bits : σ polyBits = inputBlockData w .polynomial
  coefficient_bits : σ coeffBits = inputBlockData w .coefficients
  hash_empty : σ hashBits = []

abbrev WorkState := TapeHashClean.State ⊕ TapeHorner.State
abbrev State := WorkState ⊕ TapeOutput.State

def work : TapeMultiProgram WorkState :=
  joinCode TapeHashClean.program TapeHorner.program (fun _ => TapeHorner.start)

def program : TapeMultiProgram State :=
  joinCode work TapeOutput.program (fun _ => TapeOutput.start)

def start : State := .inl (.inl TapeHashClean.start)
def done (answer : Bool) : State := .inr (TapeOutput.done answer)

def acceptFlag : State → Bool
  | .inr (.inr b) => b
  | _ => false

@[simp] theorem acceptFlag_done (b : Bool) : acceptFlag (done b) = b := rfl
@[simp] theorem program_done (b : Bool) (h : TapeHeads) : program (done b) h = none := rfl

def hashWord (w : List Bool) : List Bool :=
  List.ofFn (wordHash (decodeInput w).hashSeed (decodeInput w).data)

def evaluationWord (w : List Bool) : List Bool := List.ofFn (decodeInput w).evaluationBits

def outputStore (σ : TapeStore) (w : List Bool) : TapeStore :=
  Function.update (Function.update σ hashBits (hashWord w)) accumBits (evaluationWord w)

def cost (w : List Bool) : ℕ :=
  210 * ((decodeInput w).dataSize + (decodeInput w).ringDegree + 1) ^ 3 +
    TapeHorner.cost (decodeInput w).ringDegree (decodeInput w).coefficientCount + 7

theorem cost_le (w : List Bool) : cost w ≤ 20000 * (w.length + 1) ^ 4 := by
  let d := (decodeInput w).dataSize
  let r := (decodeInput w).ringDegree
  let t := (decodeInput w).coefficientCount
  let N := w.length + 1
  have hd : d ≤ w.length := by
    have h := five_mul_dataDimension_le w.length
    change dataDimension w.length ≤ w.length
    omega
  have hr : r ≤ d := hashDimension_le d
  have ht : t ≤ d := independenceOrder_le d
  have h3 := Nat.pow_le_pow_left (show d + r + 1 ≤ 2 * N by dsimp [N]; omega) 3
  have h4 := Nat.pow_le_pow_left (show r + t + 1 ≤ 2 * N by dsimp [N]; omega) 4
  have h34 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right (by dsimp [N]; omega) (by decide)
  have h14 : 1 ≤ N ^ 4 := by
    simpa using Nat.pow_le_pow_left (show 1 ≤ N by dsimp [N]; omega) 4
  have hH := TapeHorner.cost_le r t
  simp only [mul_pow, show (2 : ℕ) ^ 3 = 8 by decide] at h3
  simp only [mul_pow, show (2 : ℕ) ^ 4 = 16 by decide] at h4
  change 210 * (d + r + 1) ^ 3 + TapeHorner.cost r t + 7 ≤ 20000 * N ^ 4
  omega

theorem runs_evaluate_cost (w : List Bool) (σ : TapeStore)
    (hfit : InputFits w) (hprep : Prepared σ w) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg (done (language w)) (storeTapes (outputStore σ w))) (cost w) := by
  let q := decodeInput w
  let H := hashWord w
  let E := evaluationWord w
  let U := Function.update σ hashBits H
  let V := outputStore σ w
  have hhash := TapeHashClean.runs_wordHash σ q.hashSeed q.data
    hprep.data_length hprep.workspace.degree hprep.workspace.indexA_empty
    hprep.workspace.indexB_empty hprep.workspace.indexC_empty
    hprep.workspace.scratch_empty hprep.hash_empty
    (hprep.key_bits.trans (inputBlockData_hash_eq_ofFn hfit))
    (hprep.data_bits.trans (inputBlockData_data_eq_ofFn hfit))
  have hW : TapeHornerMultiply.Workspace U q.ringDegree := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [U, ringDegree, hashBits] using hprep.workspace.degree
    · simpa [U, loop0, hashBits] using hprep.workspace.loop0_empty
    · simpa [U, loop1, hashBits] using hprep.workspace.loop1_empty
    · simpa [U, indexA, hashBits] using hprep.workspace.indexA_empty
    · simpa [U, indexB, hashBits] using hprep.workspace.indexB_empty
    · simpa [U, indexC, hashBits] using hprep.workspace.indexC_empty
    · simpa [U, scratchA, hashBits] using hprep.workspace.scratch_empty
    · simpa [U, productBits, hashBits] using hprep.workspace.product_empty
  have hC : TapeHornerPrepare.Clean U := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [U, loop2, hashBits] using hprep.clean.count
    · simpa [U, loop3, hashBits] using hprep.clean.cursor
    · simpa [U, loop4, hashBits] using hprep.clean.countScratch
    · simpa [U, loop5, hashBits] using hprep.clean.mulScratch
    · simpa [U, scratchB, hashBits] using hprep.clean.coefficient
    · simpa [U, accumBits, hashBits] using hprep.clean.accumulator
  have hhorner := TapeHorner.runs_horner U (inputBlockData w .polynomial) H
    (decodedCoefficientBlocks w) q.ringDegree hW hC
    (by simp [U, hprep.polynomial_bits, polyBits, hashBits]) (by simp [U])
    (by simpa [U, hprep.coefficient_bits, coeffBits, hashBits] using
      inputBlockData_coefficients_eq_flatten hfit)
    (by simpa [U, decodedCoefficientBlocks_length, coeffCount, hashBits] using
      hprep.coefficient_count)
    (inputBlockData_polynomial_length hfit) (by simp [H, hashWord, q])
    (decodedCoefficientBlocks_row_length w)
  have hsemantic : hornerBitLists q.ringDegree (inputBlockData w .polynomial) H
      (decodedCoefficientBlocks w) = E := by
    simpa only [hashByUpdates_inputBlocks hfit, H, E, hashWord, evaluationWord, q] using
      hornerBitLists_inputBlocks hfit
  have hhorner' : RunsIn TapeHorner.program.step (cfg TapeHorner.start (storeTapes U))
      (cfg TapeHorner.done (storeTapes V)) (TapeHorner.cost q.ringDegree q.coefficientCount) := by
    simpa only [hsemantic, decodedCoefficientBlocks_length, V, outputStore, U, E, H] using hhorner
  have hwork := join_runs TapeHashClean.program TapeHorner.program
    (fun _ => TapeHorner.start) hhash rfl hhorner'
  have hlen : E.length = q.ringDegree := by simp [E, evaluationWord, q]
  have hpos : 0 < E.length := by rw [hlen]; exact decoded_ringDegree_pos hfit
  have hsplit : E = E.getD 0 false :: E.drop 1 := by
    simpa using TapeNaturalAccess.split E 0 hpos
  have hout := TapeOutput.runs_output V (E.getD 0 false) (E.drop 1)
    (by simp [V, outputStore, hprep.workspace.indexA_empty, indexA, hashBits, accumBits])
    (by simpa [V, outputStore, E] using hsplit)
  have hlanguage : language w = !(E.getD 0 false) := by
    have hl := language_eq_final_bit hfit
    rw [hashByUpdates_inputBlocks hfit] at hl
    change language w = !((hornerBitLists q.ringDegree
      (inputBlockData w .polynomial) H (decodedCoefficientBlocks w)).getD 0 false) at hl
    simpa only [hsemantic] using hl
  rw [← hlanguage] at hout
  have hall := join_runs work TapeOutput.program (fun _ => TapeOutput.start) hwork rfl hout
  have htime : (210 * (q.dataSize + q.ringDegree + 1) ^ 3 + 1 +
      TapeHorner.cost q.ringDegree q.coefficientCount) + 1 + 5 = cost w := by
    unfold cost
    dsimp [q]
    omega
  simpa only [program, start, done, htime, V] using hall

theorem runs_evaluate (w : List Bool) (σ : TapeStore)
    (hfit : InputFits w) (hprep : Prepared σ w) :
    RunsIn program.step (cfg start (storeTapes σ))
      (cfg (done (language w)) (storeTapes (outputStore σ w)))
      (20000 * (w.length + 1) ^ 4) :=
  (runs_evaluate_cost w σ hfit hprep).mono (cost_le w)

end TapeEvaluation
end DepthThreeLowerBound

end OAI
