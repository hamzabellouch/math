import OAI.Analysis.Pureness.Stabilization.MatrixBlock
import OAI.Analysis.Pureness.Stabilization.MatrixPositive

namespace OAI
noncomputable section
open scoped NNReal ENNReal Topology
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveProduct (a b : Positive A) : Positive (A × A) := ⟨(a.1,b.1),a.2,b.2⟩

omit [StarOrderedRing A] in
theorem positiveProduct_cuntzBelow {a b c d : Positive A} (hac : CuntzBelow a c) (hbd : CuntzBelow b d) :
    CuntzBelow (positiveProduct a b) (positiveProduct c d) := by
  intro ε hε
  obtain ⟨v,hv⟩ := hac ε hε
  obtain ⟨w,hw⟩ := hbd ε hε
  refine ⟨(v,w),?_⟩
  change max ‖star v*c.1*v-a.1‖ ‖star w*d.1*w-b.1‖ < ε
  exact max_lt hv hw

def matrixBlockPositive (a b : Positive (MatrixLimit A)) : Positive (MatrixLimit A) :=
  Positive.map matrixBlockHom (positiveProduct a b)

theorem matrixBlockPositive_cuntzBelow {a b c d : Positive (MatrixLimit A)}
    (hac : CuntzBelow a c) (hbd : CuntzBelow b d) :
    CuntzBelow (matrixBlockPositive a b) (matrixBlockPositive c d) :=
  (positiveProduct_cuntzBelow hac hbd).map matrixBlockHom

namespace CuntzClass

def matrixAdd (x y : CuntzClass (MatrixLimit A)) : CuntzClass (MatrixLimit A) :=
  Quotient.lift₂ (fun a b => mk (matrixBlockPositive a b))
    (fun (a b c d : Positive (MatrixLimit A)) (hac : (cuntzSetoid (MatrixLimit A)) a c)
      (hbd : (cuntzSetoid (MatrixLimit A)) b d) =>
      (mk_eq_mk_iff _ _).mpr ⟨matrixBlockPositive_cuntzBelow hac.1 hbd.1,
        matrixBlockPositive_cuntzBelow hac.2 hbd.2⟩) x y

@[simp] lemma matrixAdd_mk (a b : Positive (MatrixLimit A)) :
    matrixAdd (mk a) (mk b) = mk (matrixBlockPositive a b) := rfl

theorem matrixAdd_mono {x y u v : CuntzClass (MatrixLimit A)} (hxu : x ≤ u) (hyv : y ≤ v) :
    matrixAdd x y ≤ matrixAdd u v := by
  induction x using Quotient.inductionOn with | h a =>
  induction y using Quotient.inductionOn with | h b =>
  induction u using Quotient.inductionOn with | h c =>
  induction v using Quotient.inductionOn with | h d =>
  exact matrixBlockPositive_cuntzBelow hxu hyv
end CuntzClass
end CuntzTrace

end

end OAI
