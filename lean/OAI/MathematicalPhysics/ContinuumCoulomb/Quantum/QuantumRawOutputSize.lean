import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawCompiler
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedLabelEnergy

namespace OAI

/-! Linear size bounds for the actual emitted four-spin bond list, before
fixed-round degree reduction. All zero-weight entries are counted. -/

noncomputable section
namespace ContinuumCoulomb

private theorem flatten_map_length_bound {α β : Type} (xs : List α) (f : α → List β)
    (K : ℕ) (h : ∀ x ∈ xs, (f x).length ≤ K) :
    (xs.map f).flatten.length ≤ K*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [List.map_cons,List.flatten_cons,List.length_append,List.length_cons]
    nlinarith

namespace QuantumRawExchange

theorem fullBonds_length (n k : ℕ) (r : ℚ) (xs : List Raw) :
    (fullBonds (n,(k,r),xs)).length ≤ 6*n+22*xs.length := by
  have hp : (penalty n r).length ≤ 6*n := by
    simpa only [penalty,List.length_range] using
      flatten_map_length_bound (List.range n) (penaltyBlock r) 6
        (by intro i hi; simp only [penaltyBlock,List.length_ofFn]; exact le_rfl)
  have ht : (termBondsList ((k,r),xs)).length ≤ 22*xs.length :=
    flatten_map_length_bound xs (fun t => bonds ((k,r),t)) 22 (fun _ _ => bonds_length _)
  simpa only [fullBonds,List.length_append] using Nat.add_le_add hp ht

theorem compile_length (n N : ℕ) (xs : List Raw) :
    (compile (n,N,xs)).1.length ≤ 6*n+22*xs.length :=
  fullBonds_length n (bits (n,N,xs)) (scale N xs) xs

end QuantumRawExchange

namespace QuantumOrderedLabelCompile

theorem rawEntries_length (x : Input) : (rawEntries x).length = 12544*x.2.2.length := by
  simp only [rawEntries,Function.comp_apply,classify,List.length_map,labelEntries]
  exact QuantumOrderedLabelPipeline.output_length x

theorem output_length (x : Input) :
    (output x).1.length ≤ 6*(x.2.1+3717*x.2.2.length)+22*(12544*x.2.2.length) := by
  have h := QuantumRawExchange.compile_length (outputCount x) x.1 (rawEntries x)
  rw [rawEntries_length] at h
  simpa only [output,Function.comp_apply,rawInput,outputCount,
    QuantumOrderedLabelPipeline.output_qubits] using h

end QuantumOrderedLabelCompile

namespace QuantumPaddedLabelProgram
open QuantumOrderedSourceIndex

theorem historyOutput_length (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) :
    (historyOutput c hT N).1.length ≤
      6*(qubitCount c+3717*termCount c)+22*(12544*termCount c) := by
  have h := QuantumOrderedLabelCompile.output_length (historyInput c hT N)
  simpa only [historyOutput,historyInput,sourceEntries_length] using h

end QuantumPaddedLabelProgram
end ContinuumCoulomb

end

end OAI
