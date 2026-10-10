import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteAtomicOutputs
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourceBranchProgram

namespace OAI

/-! The decidable one-spin branch completed using arbitrary fixed YES and NO
instances, so that no atomic spectral formula is required. -/

noncomputable section
namespace ContinuumCoulomb.FiniteSourceBranch
open ExactQuantumFactoring.BitStackProgram

def value (y z : UnitCoulomb) (f : BinaryHeisenberg → UnitCoulomb)
    (d : BinaryHeisenberg) : UnitCoulomb :=
  if d.coordinate.length ≤ 1 then (if d.lower.value < 0 then z else y) else f d

noncomputable opaque program (y z : UnitCoulomb) (f : BinaryHeisenberg → UnitCoulomb)
    (pf : Procedure binaryHeisenbergCodec.encode unitCoulombCodec.encode f) :
    Procedure binaryHeisenbergCodec.encode unitCoulombCodec.encode (value y z f) := by
  let oneSpin := BisectionProgram.rationalLess.comp
    (SourcePrograms.lower.pair (Procedure.constant binaryHeisenbergCodec.encode ratCode 0))
  let small := Procedure.conditional oneSpin
    (Procedure.constant binaryHeisenbergCodec.encode unitCoulombCodec.encode z)
    (Procedure.constant binaryHeisenbergCodec.encode unitCoulombCodec.encode y)
  let test := Procedure.unaryLe.comp (SourceMetadataProgram.vertexCount.pair
    (Procedure.constant binaryHeisenbergCodec.encode unaryCode 1))
  exact (Procedure.conditional test small pf).congrFun
    (by intro d; simp only [Function.comp_apply,value,decide_eq_true_eq])

def reduction (y z : UnitCoulomb) (hy : y ∈ unitCoulombPromise.yes)
    (hz : z ∈ unitCoulombPromise.no) (k : ℕ)
    (f : BinaryHeisenberg → UnitCoulomb)
    (pf : Procedure binaryHeisenbergCodec.encode unitCoulombCodec.encode f)
    (hyes : ∀ (d : BinaryHeisenberg) (hd : d.Valid), d.PolynomialPromise k →
      2 ≤ d.coordinate.length → realSourceGroundEnergy (d.toSource hd) ≤ d.lower.value →
        f d ∈ unitCoulombPromise.yes)
    (hno : ∀ (d : BinaryHeisenberg) (hd : d.Valid), d.PolynomialPromise k →
      2 ≤ d.coordinate.length → (d.upper.value : ℝ) ≤ realSourceGroundEnergy (d.toSource hd) →
        f d ∈ unitCoulombPromise.no) :
    PolynomialManyOne binaryHeisenbergCodec.encode unitCoulombCodec.encode
      (sourceHeisenbergPromise k) unitCoulombPromise where
  map := value y z f
  polynomialTime := (program y z f pf).toTM2
  maps_yes := by
    rintro d ⟨hd,hp,hdy⟩
    have hdyR : realSourceGroundEnergy (d.toSource hd) ≤ d.lower.value := by
      apply EReal.coe_le_coe_iff.mp
      rw [realSourceGroundEnergy_coe]
      exact hdy
    by_cases hv : d.coordinate.length ≤ 1
    · have he := source_one_vertex_energy (d.toSource hd) hv
      have hl : ¬d.lower.value < 0 := not_lt.mpr
        (by exact_mod_cast (by linarith [he] : (0:ℝ) ≤ d.lower.value))
      simpa only [value,hv,hl,ite_true,ite_false] using hy
    · simpa only [value,hv,ite_false] using hyes d hd hp (by omega) hdyR
  maps_no := by
    rintro d ⟨hd,hp,hdn⟩
    have hdnR : (d.upper.value : ℝ) ≤ realSourceGroundEnergy (d.toSource hd) := by
      apply EReal.coe_le_coe_iff.mp
      rw [realSourceGroundEnergy_coe]
      exact hdn
    by_cases hv : d.coordinate.length ≤ 1
    · have he := source_one_vertex_energy (d.toSource hd) hv
      have hu : d.upper.value ≤ 0 := by
        exact_mod_cast (by linarith [he] : (d.upper.value:ℝ) ≤ 0)
      have hl : d.lower.value < 0 := lt_of_lt_of_le hd.gap hu
      simpa only [value,hv,hl,ite_true] using hz
    · simpa only [value,hv,ite_false] using hno d hd hp (by omega) hdnR

end ContinuumCoulomb.FiniteSourceBranch

end

end OAI
