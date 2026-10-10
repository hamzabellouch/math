import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingCompiled
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSelectionUnique

namespace OAI

/-! Full-space crossing error stated directly for the serialized bond packet. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingPacketEnergy
open QuantumCrossingListBlock MediatorListProgram QuantumCrossingSelectProgram
open scoped Classical

def energy (x : QuantumListPathStep.Output) : ℝ :=
  sourceMatrixBottom x.1 (SourceBondLists.matrix x.1 x.2.1+(x.2.2:ℂ) • 1)

theorem actual_energy {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    energy (QuantumCrossingListLayer.value (QuantumCrossingListLayer.actualInput C N labels))=
      (QuantumCrossingListLayer.actualGraph C N labels).energy := by
  symm
  unfold QuantumCrossingListLayer.actualGraph QuantumCrossingListLayer.graph
  rw [QuantumListGraph.ofBonds_energy]
  rfl

theorem compiled_error {G : QMARationalExchangeGraph} {r m : ℕ}
    (S : QMARationalCrossingSelection G r) (labels : G.Edge ≃ Fin m)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
    {N : ℚ} (hN : 0<N) :
    |energy (QuantumCrossingListLayer.value
      (QuantumCrossingSelectProgram.value
        (N,(G.n,QuantumListGraph.packed G labels,G.constant),List.ofFn (encodedSites S.site))))-
      G.energy|≤1/(N:ℝ) := by
  rw [QuantumCrossingSelectProgram.compiled_packet,
    actual_energy (computedLayer S labels) N (Equiv.refl _)]
  exact QuantumCrossingSelectProgram.compiled_energy_error S labels htag hN

theorem list_error (n : ℕ) (bs : List Bond) (c : ℚ)
    (hb : SourceBondLists.bounded n bs) (hn : ∀ e ∈ bs, e.1≠e.2.1)
    {r : ℕ} (site : Fin r → Fin 4 → Fin n)
    (hinj : Function.Injective (fun p : Fin r × Fin 4 => site p.1 p.2))
    {N : ℚ} (hN : 0<N) :
    |energy (QuantumCrossingListLayer.value
      (QuantumCrossingSelectProgram.value (N,(n,bs,c),List.ofFn (encodedSites site))))-
      energy (n,bs,c)|≤1/(N:ℝ) := by
  let G := QuantumListGraph.ofBonds n bs c hb hn
  have hi (i : Fin r) : Function.Injective (site i) := by
    intro a b h
    exact congrArg Prod.snd (hinj (a₁ := (i,a)) (a₂ := (i,b)) h)
  let S : QMARationalCrossingSelection G r := G.crossingSelection site hi
  have ht : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a) := by
    intro e i a
    exact G.crossingTag_some_iff site hinj e (i,a)
  have he := compiled_error S (Equiv.refl _) ht hN
  have hp : QuantumListGraph.packed G (Equiv.refl _)=bs := by
    exact List.ofFn_get bs
  rw [hp] at he
  have hge : G.energy=energy (n,bs,c) := QuantumListGraph.ofBonds_energy n bs c hb hn
  rw [hge] at he
  exact he

end ContinuumCoulomb.QuantumCrossingPacketEnergy

end

end OAI
