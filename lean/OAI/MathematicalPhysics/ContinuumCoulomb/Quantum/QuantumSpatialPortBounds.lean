import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialPortProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCoefficientPrograms

namespace OAI

/-! Coefficient and edge-count bounds for the actual port schedule tape. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPackedSchedule
open QuantumListSchedule

theorem state_coefficientBound (G : QMARationalExchangeGraph) {m : ℕ}
    (labels : G.Edge ≃ Fin m) (work : G.Edge → ℕ) {L : ℝ}
    (hc : G.CoefficientBound L) :
    (graph (state G labels work) (valid G labels work)).CoefficientBound L := by
  constructor
  · exact hc.1
  · intro i
    change |(((List.ofFn (fun j : Fin m => (work (labels.symm j),
      (G.left (labels.symm j)).val,(G.right (labels.symm j)).val,G.weight (labels.symm j)))).get i).2.2.2:ℝ)| ≤ L
    have he := List.get_ofFn (fun j : Fin m => (work (labels.symm j),
      (G.left (labels.symm j)).val,(G.right (labels.symm j)).val,G.weight (labels.symm j))) i
    exact (congrArg (fun e : QuantumListSchedule.Entry => |(e.2.2.2:ℝ)|) he).le.trans (hc.2 _)

end ContinuumCoulomb.QuantumPackedSchedule

namespace ContinuumCoulomb.QuantumSpatialPortProgram
open QuantumForkList QuantumListSchedule
open scoped Classical

variable {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D)
include hA

theorem initial_count : (initial A D (QuantumSpatialInputTape.input I)).1.2.2.length =
    Fintype.card I.model.Term := by
  have h := congrArg (fun s : QuantumListSchedule.State => s.2.2.length)
    (QuantumPortSchedulePacking.state_eq I hA)
  have hc : Fintype.card I.model.Term = (QuantumForkList.fullList I.state).length :=
    Fintype.card_fin _
  exact (h.trans (List.length_ofFn)).trans hc.symm

theorem initial_coefficientBound (hs : Valid (initial A D (QuantumSpatialInputTape.input I)).1)
    {L : ℝ} (hc : I.model.exchangeGraph.CoefficientBound L) :
    (graph (initial A D (QuantumSpatialInputTape.input I)).1 hs).CoefficientBound L := by
  have he := QuantumPortSchedulePacking.state_eq I hA
  have h := QuantumPackedSchedule.state_coefficientBound I.model.exchangeGraph (Equiv.refl _)
    (I.model.coarseLength I.model_degree) hc
  have transfer (t : QuantumListSchedule.State) (ht : Valid t)
      (e : t = QuantumPackedSchedule.state I.model.exchangeGraph (Equiv.refl _)
        (I.model.coarseLength I.model_degree)) : (graph t ht).CoefficientBound L := by
    subst t
    exact h
  exact transfer _ hs he

theorem value_bounds {N : ℚ} (hN : 0 ≤ N) {L T : ℕ} (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : I.model.exchangeGraph.CoefficientBound L) :
    ∃ hs : Valid (value A D (N,QuantumSpatialInputTape.input I)).1,
      (graph (value A D (N,QuantumSpatialInputTape.input I)).1 hs).CoefficientBound
        (QuantumCoefficientPrograms.iterated (Fintype.card I.model.Term) L T (rounds A D)) ∧
      (value A D (N,QuantumSpatialInputTape.input I)).1.2.2.length ≤
        3^(rounds A D)*Fintype.card I.model.Term := by
  let s := (initial A D (QuantumSpatialInputTape.input I)).1
  have hs : Valid s := QuantumPortSchedulePacking.valid I hA
  have hm : (s.2.2.length:ℝ) ≤ Fintype.card I.model.Term := by
    exact_mod_cast (initial_count I hA).le
  have hbound := iterate_coefficientBound hN s hs (L := (L:ℝ)) (T := (T:ℝ)) hm (by exact_mod_cast hL) hT
    (initial_coefficientBound I hA hs hc) (rounds A D)
  have hlen := iterate_edge_count N s (rounds A D)
  change (QuantumListSchedule.iterate N (rounds A D) s).2.2.length ≤
    3^(rounds A D)*(initial A D (QuantumSpatialInputTape.input I)).1.2.2.length at hlen
  rw [initial_count I hA] at hlen
  have he : (value A D (N,QuantumSpatialInputTape.input I)).1 =
      QuantumListSchedule.iterate N (rounds A D) s :=
    QuantumListRouteProgram.iterate_state N (initial A D (QuantumSpatialInputTape.input I)) (rounds A D)
  refine ⟨he.symm ▸ iterate_valid N s hs (rounds A D),?_,?_⟩
  · have transfer (t : QuantumListSchedule.State) (ht : Valid t)
        (e : t = QuantumListSchedule.iterate N (rounds A D) s) :
        (graph t ht).CoefficientBound
          (QuantumCoefficientPrograms.iterated (Fintype.card I.model.Term) L T (rounds A D)) := by
      subst t
      simpa only [QuantumCoefficientPrograms.iterated_cast] using hbound
    exact transfer _ _ he
  · exact (congrArg (fun t : QuantumListSchedule.State => t.2.2.length) he).le.trans hlen

end ContinuumCoulomb.QuantumSpatialPortProgram

end

end OAI
