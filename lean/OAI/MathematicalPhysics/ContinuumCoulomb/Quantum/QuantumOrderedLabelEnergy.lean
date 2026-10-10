import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelCompile
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedXZEnergy

namespace OAI

/-! Full-space energy guarantee for the emitted raw exchange list, with
the five early reductions, private-pair subdivision, and four-spin error
all accounted for. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelCompile
open QuantumOrderedLabelTable
open scoped Classical

def outputEnergy (x : Input) : ℝ :=
  MediatorGraph.normalizedBottom (QuantumRawExchange.rawMatrix (qubitCount x) (output x))

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {m n : ℕ}

def finalEnergy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ) (N : ℕ) : ℝ :=
  MediatorGraph.normalizedBottom (qmaPauliFamily (finalWord xs w)
    (fun p => (finalCoefficient J N p:ℝ)))

theorem compiled_final_error (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hx : ∀ a, (xs a).Nodup)
    (hcover : ∀ a, qmaPauliSupport (w a) ⊆ (xs a).toFinset)
    (he : ∀ a, Even (qmaPauliYCount (w a))) (N : ℕ) (hN : 0 < N) :
    |outputEnergy (N,n,table e (index q) xs w J)-finalEnergy xs w J N| ≤ 2/(N:ℝ) := by
  let qf := qubits6 q e
  let ef := terms6 e
  have hlenF : ∀ p, (finalSites xs w p).length ≤ 2 :=
    QuantumOrderedPrivate.outputSites_length _ (QuantumOrderedXZ.sites_length xs w hlen)
  have hxF : ∀ p, (finalSites xs w p).Nodup :=
    QuantumOrderedPrivate.outputSites_nodup _ (QuantumOrderedXZ.sites_nodup xs w hlen hx)
  have hsF : ∀ p, qmaPauliSupport (finalWord xs w p) ⊆ (finalSites xs w p).toFinset :=
    QuantumOrderedPrivate.outputSites_cover _ _
  have hyF : ∀ p i, finalWord xs w p i ≠ 2 :=
    QuantumOrderedPrivate.output_noY _ _ (QuantumOrderedXZ.noY xs w hlen hx hcover he)
  have hpF : ∀ p r, (qmaPauliSupport (finalWord xs w p)).card=2 →
      qmaPauliSupport (finalWord xs w p)=qmaPauliSupport (finalWord xs w r) → p=r :=
    QuantumOrderedPrivate.output_private _ _ (QuantumOrderedXZ.sites_nodup xs w hlen hx)
  have hr := QuantumOrderedRawBlock.output_accuracy N hN
    (numberedSites qf ef (finalSites xs w)) (numberedWord qf ef (finalWord xs w))
    (fun i => finalCoefficient J N (ef i))
    (fun i => (numbered_sites_length qf ef _ i).trans_le (hlenF (ef i)))
    (numbered_sites_nodup qf ef _ hxF) (numbered_cover qf ef _ _ hsF)
    (fun i j => hyF (ef i) (qf j)) (numbered_private qf ef _ hpF)
  have hn : qubitCount (N,n,table e (index q) xs w J)=finalCount n m*4 := by
    rw [qubitCount_table,finalCount_eq]
    omega
  unfold outputEnergy
  rw [hn,output_table q e xs w J hlen hx N]
  unfold finalEnergy
  rw [← numbered_energy qf ef (finalWord xs w) (fun p => (finalCoefficient J N p:ℝ))]
  exact hr

theorem final_xz_error (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hx : ∀ a, (xs a).Nodup)
    (N : ℕ) (hN : 0 < N) :
    |finalEnergy xs w J N-QuantumOrderedXZ.energy xs w J N| ≤ 1/(N:ℝ) :=
  QuantumOrderedPrivate.output_accuracy _ _ _ (QuantumOrderedXZ.sites_nodup xs w hlen hx)
    (QuantumOrderedXZ.sites_cover xs w) N (by omega)

theorem output_accuracy (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hx : ∀ a, (xs a).Nodup)
    (hcover : ∀ a, qmaPauliSupport (w a) ⊆ (xs a).toFinset)
    (he : ∀ a, Even (qmaPauliYCount (w a))) (N : ℕ) (hN : 0 < N) :
    |outputEnergy (N,n,table e (index q) xs w J)-
      MediatorGraph.normalizedBottom (qmaPauliFamily w (fun a => (J a:ℝ)))| ≤ 8/(N:ℝ) := by
  have h₁ := compiled_final_error q e xs w J hlen hx hcover he N hN
  have h₂ := final_xz_error xs w J hlen hx N hN
  have h₃ := QuantumOrderedXZ.accuracy xs w J hlen hx hcover he N (by omega)
  exact (abs_sub_le _ (finalEnergy xs w J N) _).trans
    ((add_le_add h₁ ((abs_sub_le _ (QuantumOrderedXZ.energy xs w J N) _).trans
      (add_le_add h₂ h₃))).trans_eq (by ring))

end ContinuumCoulomb.QuantumOrderedLabelCompile

end

end OAI
