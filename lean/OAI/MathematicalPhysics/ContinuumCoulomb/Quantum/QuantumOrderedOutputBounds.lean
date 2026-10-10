import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawEnvelope
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedFinalBounds

namespace OAI

/-! The polynomial envelopes apply to the actual emitted rational graph,
with the same six-stage table and four-spin instructions used by its energy proof. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelCompile
open QuantumOrderedLabelTable
open scoped Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {n m : ℕ}

theorem rawInput_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hdup : ∀ a, (xs a).Nodup) (N : ℕ) :
    rawInput (N,n,table e (index q) xs w J) =
      (finalCount n m,N,QuantumRawExchange.packed
        (QuantumOrderedRawBlock.terms
          (numberedSites (qubits6 q e) (terms6 e) (finalSites xs w))
          (numberedWord (qubits6 q e) (terms6 e) (finalWord xs w)))
        (fun i => finalCoefficient J N (terms6 e i))) := by
  unfold rawInput outputCount rawEntries labelEntries classify
  simp only [Function.comp_apply,QuantumOrderedLabelTable.output_table q e xs w J hlen hdup N]
  rw [packed_table]
  rfl

def coefficientEnvelope (n m B N : ℕ) : ℕ := QuantumRawExchange.outputNat
  (n+3717*m) (12544*m) (QuantumOrderedXZ.pipelineNat m B N 6) N

omit [DecidableEq κ] in
theorem final_raw_weights (e : Fin m ≃ κ) (J : κ → ℚ) {B : ℕ}
    (hJ : ∀ p, |J p| ≤ (B:ℚ)) (N : ℕ) :
    ∀ i, |(finalCoefficient J N (terms6 e i):ℝ)| ≤ QuantumOrderedXZ.pipelineNat m B N 6 := by
  have hm : Fintype.card κ ≤ m := le_of_eq ((Fintype.card_congr e).symm.trans (Fintype.card_fin m))
  intro i
  exact_mod_cast QuantumOrderedXZ.private_coefficient_bound J hm hJ N (terms6 e i)

theorem output_coefficients (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hdup : ∀ a, (xs a).Nodup)
    {B : ℕ} (hJ : ∀ p, |J p| ≤ (B:ℚ)) (N : ℕ) :
    |((output (N,n,table e (index q) xs w J)).2:ℝ)| ≤ coefficientEnvelope n m B N ∧
      ∀ b ∈ (output (N,n,table e (index q) xs w J)).1,
        |(b.2.2:ℝ)| ≤ coefficientEnvelope n m B N := by
  let t := QuantumOrderedRawBlock.terms
    (numberedSites (qubits6 q e) (terms6 e) (finalSites xs w))
    (numberedWord (qubits6 q e) (terms6 e) (finalWord xs w))
  let c := fun i => finalCoefficient J N (terms6 e i)
  let bs := QuantumRawExchange.packed t c
  have hlenbs : bs.length=12544*m := by
    simp only [bs,QuantumRawExchange.packed,List.length_ofFn]
    ring
  have hw : ∀ b ∈ bs, |(b.2.2.2:ℝ)| ≤ QuantumOrderedXZ.pipelineNat m B N 6 := by
    intro b hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    rw [QuantumRawExchange.pack_weight]
    exact final_raw_weights e J hJ N i
  change _ ≤ (coefficientEnvelope n m B N:ℝ) ∧ _
  unfold output
  simp only [Function.comp_apply]
  rw [rawInput_table q e xs w J hlen hdup N]
  constructor
  · have h := QuantumRawExchange.compile_scalar_bound (finalCount n m) N
      (QuantumOrderedXZ.pipelineNat m B N 6) bs hw
    rw [hlenbs] at h
    conv at h => rhs; rw [finalCount_eq]
    exact h
  · intro b hb
    have h := QuantumRawExchange.compile_bond_bound (finalCount n m) N
      (QuantumOrderedXZ.pipelineNat m B N 6) bs hw b hb
    rw [hlenbs] at h
    conv at h => rhs; rw [finalCount_eq]
    exact h

end ContinuumCoulomb.QuantumOrderedLabelCompile

end

end OAI
