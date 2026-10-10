import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialPlanarBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialFinalCount
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvenTapeOutputBounds

namespace OAI

/-! Polynomial promise of the actual emitted lattice packet from the
fixed spatial graph, using its uniform coefficient and geometric bounds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFinalRoutingProgram
open QuantumForkList QuantumCoefficientPrograms
open scoped Classical

theorem spatial_polynomialPromise {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) {N : ℚ} (hN : 0 < N)
    {L T n k : ℕ} (hn : 0 < I.model.n) (hsize : n ≤ I.model.n)
    (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : I.model.exchangeGraph.CoefficientBound L)
    (a b : ℚ) (hab : a < b)
    (hx : (256*I.model.bufferedWidth:ℕ) ≤ (n+1:ℝ)^k)
    (hy : (256*I.model.bufferedHeight:ℕ) ≤ (n+1:ℝ)^k)
    (hw : (latticeBound (QuantumSpatialPortProgram.rounds A D) (Fintype.card I.model.Term)
      (I.model.portRouteData hA I.model_degree).crossingCells.card L T:ℝ) ≤ (n+1:ℝ)^k)
    (hgap : ((n+1:ℝ)^k)⁻¹ ≤ (b:ℝ)-a) :
    (value A D ((N,QuantumSpatialInputTape.input I),a,b)).PolynomialPromise k := by
  let P := I.model.portRouteData hA I.model_degree
  let x := QuantumSpatialCrossingProgram.value A D (N,QuantumSpatialInputTape.input I)
  have hg := QuantumSpatialCrossingProgram.packet_geometry I hA N
  have hp : ∀ e j, j ≤ P.length e →
      (P.point e j).1 < I.model.bufferedWidth ∧ (P.point e j).2 < I.model.bufferedHeight := by
    intro e j _
    exact I.model.bufferedPath_bounds I.model_degree e
      ((I.model.bufferedPath I.model_degree e).val.getVert_mem_support j)
  obtain ⟨R,hinput,hR,hbox⟩ := QuantumPlanarTapeGeometry.planar_family P N
    (QuantumSpatialCrossingProgram.length_bound I hA) x hg
    (QuantumSpatialCrossingProgram.table_permission I hA N)
    (I.model.sourceCell_no_passage hA I.model_degree) I.model.placedVertex_positive
    I.model.placedVertex_bounds hp
  let m₁ := 3^(QuantumSpatialPortProgram.rounds A D)*Fintype.card I.model.Term
  let B := iterated (Fintype.card I.model.Term) L T (QuantumSpatialPortProgram.rounds A D)
  let m₂ := m₁+9*P.crossingCells.card
  let C := (m₂+1)*crossingCoefficient m₁ P.crossingCells.card ((m₁+1)*B) T
  obtain ⟨hC,hm⟩ := QuantumSpatialCrossingProgram.planar_bounds I hA hN.le hL hT hc hg.noLoops
  have hnR : 0 < (QuantumPlanarTapeGeometry.graph x hg.noLoops).n :=
    hn.trans_le (spatial_crossing_count_le I hA N)
  have hsR : n ≤ (QuantumPlanarTapeGeometry.graph x hg.noLoops).n :=
    hsize.trans (spatial_crossing_count_le I hA N)
  have hC1 : 1 ≤ C := by
    have h := crossingCoefficient_one m₁ P.crossingCells.card ((m₁+1)*B) T
    exact Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le m₂)) h
  have hC' : (QuantumPlanarTapeGeometry.graph x hg.noLoops).CoefficientBound (C:ℝ) := by
    simpa only [C,m₂,m₁,B,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hC
  have h := QuantumEvenTapeGeometry.output_polynomialPromise R (Equiv.refl _)
    hN hR hbox hnR hm hC1 hT hC' hsR a b hab
    (by simpa only [← Nat.mul_assoc,show 8*32=256 by decide] using hx)
    (by simpa only [← Nat.mul_assoc,show 8*32=256 by decide] using hy)
    (show ((3^81*m₂+1)*iterated (3*m₂) (pathCoefficient m₂ C T) T 80:ℕ) ≤
      (n+1:ℝ)^k from hw) hgap
  rw [← hinput] at h
  exact h

end ContinuumCoulomb.QuantumFinalRoutingProgram

end

end OAI
