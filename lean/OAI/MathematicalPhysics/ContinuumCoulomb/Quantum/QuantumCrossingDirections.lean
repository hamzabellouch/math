import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPorts
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridNeighborsFour
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedBounds

namespace OAI

/-! The four crossing ports form a permutation of the four lattice directions. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaGridPorts_permutation {z : ℕ × ℕ} (hx : 0 < z.1) (hy : 0 < z.2)
    (port : Fin 4 → ℕ × ℕ) (hi : Function.Injective port)
    (ha : ∀ i, qmaSquareGrid.Adj z (port i)) :
    ∃ σ : Fin 4 ≃ Fin 4, ∀ i, port i = qmaGridNeighbor z (σ i) := by
  let index := fun i => qmaGridNeighborIndex z (port i)
  have he (i) : qmaGridNeighbor z (index i) = port i := qmaGridNeighborIndex_spec hx hy (ha i)
  have hinj : Function.Injective index := by
    intro i j h
    apply hi
    rw [← he i,← he j,h]
  let σ : Fin 4 ≃ Fin 4 := Equiv.ofBijective index ⟨hinj,Finite.surjective_of_injective hinj⟩
  exact ⟨σ,fun i => (he i).symm⟩

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem buffered_crossing_directions (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) {e f : M.Term} (hef : e ≠ f)
    {z : ℕ × ℕ} (hv : ∀ v, z ≠ M.placedVertex v)
    (he : z ∈ (M.bufferedPath hd e).val.support)
    (hf : z ∈ (M.bufferedPath hd f).val.support) :
    ∃ σ : Fin 4 ≃ Fin 4,
      s(z,qmaGridNeighbor z (σ 0)) ∈ (M.bufferedPath hd e).val.edges ∧
      s(z,qmaGridNeighbor z (σ 1)) ∈ (M.bufferedPath hd e).val.edges ∧
      s(z,qmaGridNeighbor z (σ 2)) ∈ (M.bufferedPath hd f).val.edges ∧
      s(z,qmaGridNeighbor z (σ 3)) ∈ (M.bufferedPath hd f).val.edges := by
  obtain ⟨port,hi,ha,h0,h1,h2,h3⟩ := M.buffered_crossing_ports hA hd hef hv he hf
  have hp := M.bufferedPath_positive hd e he
  obtain ⟨σ,hσ⟩ := qmaGridPorts_permutation hp.1 hp.2 port hi ha
  refine ⟨σ,?_,?_,?_,?_⟩
  · simpa only [hσ] using h0
  · simpa only [hσ] using h1
  · simpa only [hσ] using h2
  · simpa only [hσ] using h3

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
