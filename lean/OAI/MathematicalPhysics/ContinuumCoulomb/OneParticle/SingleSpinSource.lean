import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.AtomicOutputs
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourceMetadataProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.BisectionProgram

namespace OAI

/-! A literal, constant-size decision branch covers the original one-spin
source. This prevents the many-electron construction from excluding it. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem source_one_vertex_edges (d : SquareLatticeHeisenberg) (hv : d.vertices ≤ 1) : d.edges=0 := by
  apply Nat.eq_zero_of_not_pos
  intro he
  let e : Fin d.edges := ⟨0,he⟩
  have hn := d.edge_ne e
  have hl := (d.left e).isLt
  have hr := (d.right e).isLt
  exact hn (Fin.ext (by omega))

theorem source_one_vertex_energy (d : SquareLatticeHeisenberg) (hv : d.vertices ≤ 1) :
    realSourceGroundEnergy d=0 := by
  have he := source_one_vertex_edges d hv
  let : IsEmpty (Fin d.edges) := Fin.isEmpty_iff.mpr he
  have hf (w : SourceSpinVector d.vertices) : sourceHamiltonianForm d w=0 := by
    simp [sourceHamiltonianForm]
  apply le_antisymm
  · simpa only [hf] using realSourceGroundEnergy_le_trial d (allUpSourceVector d.vertices)
      (allUpSourceVector_mass d.vertices)
  · exact realSourceGroundEnergy_lower_of_forall d 0 (fun w _ => (hf w).ge)

namespace SingleSpinSource
open ExactQuantumFactoring.BitStackProgram

def value (d : BinaryHeisenberg) : UnitCoulomb :=
  if d.lower.value < 0 then atomicOutput false else atomicOutput true

noncomputable opaque program : Procedure binaryHeisenbergCodec.encode unitCoulombCodec.encode value := by
  let test := BisectionProgram.rationalLess.comp
    (SourcePrograms.lower.pair (Procedure.constant binaryHeisenbergCodec.encode ratCode 0))
  exact (Procedure.conditional test
    (Procedure.constant binaryHeisenbergCodec.encode unitCoulombCodec.encode (atomicOutput false))
    (Procedure.constant binaryHeisenbergCodec.encode unitCoulombCodec.encode (atomicOutput true))).congrFun
      (by intro d; simp only [Function.comp_apply,value,decide_eq_true_eq])

theorem yes (hh : PublishedHydrogenBottom) (d : BinaryHeisenberg) (hd : d.Valid)
    (hv : d.coordinate.length ≤ 1)
    (hy : realSourceGroundEnergy (d.toSource hd) ≤ d.lower.value) : value d ∈ unitCoulombPromise.yes := by
  have he := source_one_vertex_energy (d.toSource hd) hv
  have hl : ¬d.lower.value < 0 := not_lt.mpr (by exact_mod_cast (by linarith [he] : (0:ℝ) ≤ d.lower.value))
  simp only [value,hl,ite_false]
  exact atomicOutput_yes hh

theorem no (hh : PublishedHydrogenBottom) (d : BinaryHeisenberg) (hd : d.Valid)
    (hv : d.coordinate.length ≤ 1)
    (hn : (d.upper.value:ℝ) ≤ realSourceGroundEnergy (d.toSource hd)) : value d ∈ unitCoulombPromise.no := by
  have he := source_one_vertex_energy (d.toSource hd) hv
  have hu : d.upper.value ≤ 0 := by exact_mod_cast (by linarith [he] : (d.upper.value:ℝ) ≤ 0)
  have hl : d.lower.value < 0 := lt_of_lt_of_le hd.gap hu
  simp only [value,hl,ite_true]
  exact atomicOutput_no hh

end SingleSpinSource
end ContinuumCoulomb

end

end OAI
