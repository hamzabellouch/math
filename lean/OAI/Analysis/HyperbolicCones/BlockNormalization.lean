import OAI.Analysis.HyperbolicCones.RawBlocks
import OAI.Analysis.HyperbolicCones.CongruenceMaps

namespace OAI

/-! Fixed positive-definite diagonal congruence makes both positive maps unital. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Set
namespace Paper256

noncomputable def RawBlockPencil.normalize {K : Set Ambient} (P : RawBlockPencil K) :
    BlockPencil K := by
  let S := inverseSquareRoot (P.D 1)
  let T := inverseSquareRoot (P.E 1)
  refine {
    a := P.a
    c := P.c
    a_pos := P.a_pos
    c_pos := P.c_pos
    D := (congruenceSym S).comp P.D
    E := (congruenceSym T).comp P.E
    F := (congruenceSym S).comp P.F
    C := (congruenceRect S T).comp P.C
    A := (congruenceSym S).comp P.A
    B := (congruenceRect S T).comp P.B
    G := (congruenceSym T).comp P.G
    D_positive := fun X hX => congruenceSym_positive S (P.D X) (P.D_positive X hX)
    E_positive := fun Z hZ => congruenceSym_positive T (P.E Z) (P.E_positive Z hZ)
    D_unital := congruenceSym_inverseSquareRoot_self (P.D 1) P.D_identity_posDef
    E_unital := congruenceSym_inverseSquareRoot_self (P.E 1) P.E_identity_posDef
    represents := ?_ }
  intro X Z y
  rw [P.represents]
  have h := block_congruence_posSemidef_iff S T
    (inverseSquareRoot_isUnit (P.D 1) P.D_identity_posDef)
    (inverseSquareRoot_isUnit (P.E 1) P.E_identity_posDef)
    ((P.D X : Mat P.a ℝ) + (P.F Z : Mat P.a ℝ) + (P.A y : Mat P.a ℝ))
    (P.C Z + P.B y) ((P.E Z : Mat P.c ℝ) + (P.G y : Mat P.c ℝ))
  simpa only [LinearMap.comp_apply, congruenceSym_val, congruenceRect_apply,
    Matrix.mul_add, Matrix.add_mul] using h.symm

end Paper256

end

end OAI
