import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SingleSpinSource
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePositiveCorrectness
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.UnitBinaryProgram

namespace OAI

/-! Literal completion of a many-spin source map on the one-spin branch.
The resulting reduction covers every valid source instance. -/

noncomputable section
namespace ContinuumCoulomb.SourceBranchProgram
open ExactQuantumFactoring.BitStackProgram

def value (f : BinaryHeisenberg → UnitCoulomb) (d : BinaryHeisenberg) : UnitCoulomb :=
  if d.coordinate.length ≤ 1 then SingleSpinSource.value d else f d

noncomputable opaque program (f : BinaryHeisenberg → UnitCoulomb)
    (pf : Procedure binaryHeisenbergCodec.encode unitCoulombCodec.encode f) :
    Procedure binaryHeisenbergCodec.encode unitCoulombCodec.encode (value f) := by
  let test := Procedure.unaryLe.comp (SourceMetadataProgram.vertexCount.pair
    (Procedure.constant binaryHeisenbergCodec.encode unaryCode 1))
  exact (Procedure.conditional test SingleSpinSource.program pf).congrFun
    (by intro d; simp only [Function.comp_apply,value,decide_eq_true_eq])

theorem positive_output_vertices (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (hv : 2 ≤ d.coordinate.length) : 2 ≤ (SourcePositiveProgram.output s d).vertices := by
  rw [SourcePositiveProgram.vertices_eq s d hd]
  omega

def reduction (hh : PublishedHydrogenBottom) (k : ℕ)
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
  map := value f
  polynomialTime := (program f pf).toTM2
  maps_yes := by
    rintro d ⟨hd,hp,hy⟩
    have hyR : realSourceGroundEnergy (d.toSource hd) ≤ d.lower.value := by
      apply EReal.coe_le_coe_iff.mp
      rw [realSourceGroundEnergy_coe]
      exact hy
    by_cases hv : d.coordinate.length ≤ 1
    · simpa only [value,hv,ite_true] using SingleSpinSource.yes hh d hd hv hyR
    · simpa only [value,hv,ite_false] using hyes d hd hp (by omega) hyR
  maps_no := by
    rintro d ⟨hd,hp,hn⟩
    have hnR : (d.upper.value : ℝ) ≤ realSourceGroundEnergy (d.toSource hd) := by
      apply EReal.coe_le_coe_iff.mp
      rw [realSourceGroundEnergy_coe]
      exact hn
    by_cases hv : d.coordinate.length ≤ 1
    · simpa only [value,hv,ite_true] using SingleSpinSource.no hh d hd hv hnR
    · simpa only [value,hv,ite_false] using hno d hd hp (by omega) hnR

end ContinuumCoulomb.SourceBranchProgram

end

end OAI
