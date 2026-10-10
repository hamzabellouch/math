import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLatticeEncoding
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpecifiedLattice
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceEncodingSize

namespace OAI

/-! The actual lattice serialization preserves the source energy promise.
Numerical envelopes may be measured against any retained input size; the
output bit length is at least the number of physical spins. -/

noncomputable section
namespace ContinuumCoulomb
open ExactQuantumFactoring.BitStackProgram

namespace SquareLatticeHeisenberg

/-- The literal serializer receives precisely the finite data of this source. -/
def binaryPacket (d : SquareLatticeHeisenberg) : QuantumLatticeSerialization.Input :=
  (List.ofFn d.coordinate,
    List.ofFn (fun e => ((d.left e).val,(d.right e).val,d.coefficient e)),
    d.lower,d.upper,0)

theorem binaryPacket_value (d : SquareLatticeHeisenberg) :
    QuantumLatticeSerialization.value d.binaryPacket = d.binary := by
  have he : (List.ofFn (fun e => ((d.left e).val,(d.right e).val,d.coefficient e))).map
      QuantumLatticeSerialization.edge = List.ofFn d.binaryEdge := by
    rw [List.map_ofFn]
    rfl
  change BinaryHeisenberg.mk _ _ _ _ = BinaryHeisenberg.mk _ _ _ _
  dsimp only [binaryPacket]
  rw [he]
  simp only [sub_zero]

theorem binary_polynomialPromise (d : SquareLatticeHeisenberg) (n k : ℕ)
    (hn : n ≤ d.vertices)
    (hc : ∀ i, |((d.coordinate i).1 : ℝ)| ≤ (n+1:ℝ)^k ∧
      |((d.coordinate i).2 : ℝ)| ≤ (n+1:ℝ)^k)
    (hJ : ∀ e, |(d.coefficient e : ℝ)| ≤ (n+1:ℝ)^k)
    (hg : ((n+1:ℝ)^k)⁻¹ ≤ (d.upper:ℝ)-d.lower) :
    d.binary.PolynomialPromise k := by
  have hsize : n ≤ (binaryHeisenbergCodec.encode d.binary).length := by
    have h := binaryHeisenberg_count_le_length d.binary
    rw [d.binary_vertices] at h
    omega
  have hbase : (n+1:ℝ) ≤ ((binaryHeisenbergCodec.encode d.binary).length+1:ℝ) := by
    exact_mod_cast Nat.add_le_add_right hsize 1
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ n+1) hbase k
  constructor
  · intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact ⟨(hc i).1.trans hpow,(hc i).2.trans hpow⟩
  · intro e
    rw [d.binary_getEdge e]
    simp only [binaryEdge,BinaryRational.value_ofRat]
    exact (hJ ⟨e.val,by simpa using e.isLt⟩).trans hpow
  · simp only [binary_lower,binary_upper]
    exact (inv_anti₀ (by positivity : (0:ℝ) < (n+1)^k) hpow).trans hg

theorem binary_mem_yes (d : SquareLatticeHeisenberg) {k : ℕ}
    (hp : d.binary.PolynomialPromise k) (he : realSourceGroundEnergy d ≤ (d.lower:ℝ)) :
    d.binary ∈ (sourceHeisenbergPromise k).yes := by
  refine ⟨d.binary_valid,hp,?_⟩
  rw [d.binary_toSource,← realSourceGroundEnergy_coe,d.binary_lower]
  exact EReal.coe_le_coe he

theorem binary_mem_no (d : SquareLatticeHeisenberg) {k : ℕ}
    (hp : d.binary.PolynomialPromise k) (he : (d.upper:ℝ) ≤ realSourceGroundEnergy d) :
    d.binary ∈ (sourceHeisenbergPromise k).no := by
  refine ⟨d.binary_valid,hp,?_⟩
  rw [d.binary_toSource,← realSourceGroundEnergy_coe,d.binary_upper]
  exact EReal.coe_le_coe he

end SquareLatticeHeisenberg

namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
variable (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D)
variable (havoid : ∀ i : P.Interior, ∀ v, P.cell i ≠ P.position v)
variable (hpositive : ∀ v, 0 < (P.position v).1 ∧ 0 < (P.position v).2)

/-- Preserve a positive gap by moving both thresholds inward by the proved
simulation error, before removing the exact scalar matrix offset. -/
def marginSource (hn : 0 < G.n) (a b ε : ℚ) (hab : a+ε < b-ε) : SquareLatticeHeisenberg :=
  P.latticeSource N hD havoid hpositive hn (a+ε) (b-ε) hab

theorem marginSource_yes (hN : 0 < N) (hn : 0 < G.n) (a b ε : ℚ)
    (hab : a+ε < b-ε) (hε : ((D+82:ℕ):ℝ)/(N:ℝ) ≤ (ε:ℝ))
    (he : G.energy ≤ (a:ℝ)) :
    realSourceGroundEnergy (P.marginSource N hD havoid hpositive hn a b ε hab) ≤
      ((P.marginSource N hD havoid hpositive hn a b ε hab).lower:ℝ) := by
  have h := (abs_le.mp (P.lattice_energy_error N hD havoid hpositive hN)).2
  rw [marginSource,P.latticeSource_energy]
  change _ ≤ ((a+ε-(P.latticeGraph N hD havoid hpositive).constant:ℚ):ℝ)
  push_cast
  linarith

theorem marginSource_no (hN : 0 < N) (hn : 0 < G.n) (a b ε : ℚ)
    (hab : a+ε < b-ε) (hε : ((D+82:ℕ):ℝ)/(N:ℝ) ≤ (ε:ℝ))
    (he : (b:ℝ) ≤ G.energy) :
    ((P.marginSource N hD havoid hpositive hn a b ε hab).upper:ℝ) ≤
      realSourceGroundEnergy (P.marginSource N hD havoid hpositive hn a b ε hab) := by
  have h := (abs_le.mp (P.lattice_energy_error N hD havoid hpositive hN)).1
  rw [marginSource,P.latticeSource_energy]
  change ((b-ε-(P.latticeGraph N hD havoid hpositive).constant:ℚ):ℝ) ≤ _
  push_cast
  linarith

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
