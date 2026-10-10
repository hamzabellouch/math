import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialPortBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialCrossingSupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMergedCoefficientBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLatticeCoefficient

namespace OAI

/-! The actual merged crossing packet satisfies the same polynomial
envelope as the physical construction, including parallel-edge sums. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialCrossingProgram
open QuantumForkList QuantumCrossingSelectProgram QuantumCoefficientPrograms
open scoped Classical

theorem planar_bounds {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) {N : ℚ} (hN : 0 ≤ N) {L T : ℕ}
    (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : I.model.exchangeGraph.CoefficientBound L)
    (hn : ∀ e ∈ (value A D (N,QuantumSpatialInputTape.input I)).1.1.2.1, e.1 ≠ e.2.1) :
    let K := QuantumSpatialPortProgram.rounds A D
    let m := 3^K*Fintype.card I.model.Term
    let r := (I.model.portRouteData hA I.model_degree).crossingCells.card
    let B := iterated (Fintype.card I.model.Term) L T K
    (QuantumPlanarTapeGeometry.graph (value A D (N,QuantumSpatialInputTape.input I)) hn).CoefficientBound
      ((m+9*r+1)*crossingCoefficient m r ((m+1)*B) T) ∧
    Fintype.card (QuantumPlanarTapeGeometry.graph
      (value A D (N,QuantumSpatialInputTape.input I)) hn).Edge ≤ m+9*r := by
  let P := I.model.portRouteData hA I.model_degree
  let s := (QuantumSpatialPortProgram.value A D (N,QuantumSpatialInputTape.input I)).1
  obtain ⟨hs,hC,hcount⟩ := QuantumSpatialPortProgram.value_bounds I hA hN hL hT hc
  obtain ⟨σ,τ,hsite,_⟩ := sites_positions_order I hA N
  let site := fun i a => σ.symm (P.crossingSiteFin N (length_bound I hA) (τ i) a)
  have hsi (i) : Function.Injective (site i) := by
    intro a b hab
    exact P.crossingSiteFin_injective N (length_bound I hA) (τ i) (σ.symm.injective hab)
  let H := QuantumListSchedule.graph s hs
  let S := H.crossingSelection site hsi
  have hx : (value A D (N,QuantumSpatialInputTape.input I)).1.1 =
      QuantumCrossingListLayer.value
        (QuantumCrossingListLayer.actualInput (computedLayer S (Equiv.refl _)) N (Equiv.refl _)) := by
    have hp := QuantumListSchedule.graph_packed s hs
    have h := compiled_packet S (Equiv.refl _) N
    have hh := congrArg (fun bs => QuantumCrossingSelectProgram.value
      (N,(s.1,bs,s.2.1),List.ofFn (encodedSites site))) hp.symm
    have hv := congrArg QuantumCrossingListLayer.value (hh.trans h)
    change QuantumCrossingListLayer.value (QuantumCrossingSelectProgram.value
      (N,oldPacket A D (N,QuantumSpatialInputTape.input I),
        sites A D (N,QuantumSpatialInputTape.input I))) = _
    rw [hsite]
    exact hv
  have hm : Fintype.card H.Edge ≤ 3^(QuantumSpatialPortProgram.rounds A D)*Fintype.card I.model.Term := by
    simpa only [H,QuantumListSchedule.graph,Fintype.card_fin] using hcount
  have hB : 1 ≤ iterated (Fintype.card I.model.Term) L T (QuantumSpatialPortProgram.rounds A D) :=
    iterated_one hL _ _ _
  have h := compiled_planar_nat S (Equiv.refl _) hN hm hB hT hC
    (value A D (N,QuantumSpatialInputTape.input I)) hx hn
  have hr : (cells A D (N,QuantumSpatialInputTape.input I)).length = P.crossingCells.card :=
    (Fintype.card_fin _).symm.trans ((Fintype.card_congr τ).trans (Fintype.card_fin _))
  simpa only [hr] using h

end ContinuumCoulomb.QuantumSpatialCrossingProgram

end

end OAI
