import OAI.Analysis.Pureness.Stabilization.MatrixSums
import OAI.Analysis.Pureness.Stabilization.CuntzClass

namespace OAI
noncomputable section
open scoped NNReal ENNReal Topology
namespace CuntzTrace
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem CuntzBelow.map (f : A →⋆ₙₐ[ℂ] B) {a b : Positive A} (h : CuntzBelow a b) :
    CuntzBelow (Positive.map f a) (Positive.map f b) := by
  intro ε hε
  obtain ⟨v,hv⟩ := h ε hε
  refine ⟨f v, ?_⟩
  change ‖star (f v)*f b.1*f v-f a.1‖ < ε
  rw [← map_star, ← map_mul, ← map_mul, ← map_sub]
  exact (NonUnitalStarAlgHom.norm_apply_le f _).trans_lt hv

namespace CuntzClass
def map (f : A →⋆ₙₐ[ℂ] B) : CuntzClass A →o CuntzClass B where
  toFun := Quotient.lift (fun a => mk (Positive.map f a)) (fun a b h =>
    (mk_eq_mk_iff _ _).mpr ⟨h.1.map f, h.2.map f⟩)
  monotone' := by
    intro x y
    exact Quotient.inductionOn₂ x y (fun a b h => (mk_le_mk _ _).mpr (h.map f))
@[simp] lemma map_mk (f : A →⋆ₙₐ[ℂ] B) (a : Positive A) : map f (mk a) = mk (Positive.map f a) := rfl
end CuntzClass

omit [StarOrderedRing A] in
theorem positivePair_cuntzBelow {a b c d : Positive A} (hac : CuntzBelow a c) (hbd : CuntzBelow b d) :
    CuntzBelow (positivePair a b) (positivePair c d) := by
  intro ε hε
  obtain ⟨v,hv⟩ := hac ε hε
  obtain ⟨w,hw⟩ := hbd ε hε
  let z : Fin 2 → A := ![v,w]
  refine ⟨z, ?_⟩
  change ‖(fun i => star (z i) * (positivePair c d).1 i * z i - (positivePair a b).1 i)‖ < ε
  apply (pi_norm_lt_iff hε).mpr
  intro i
  fin_cases i
  · simpa [z, positivePair] using hv
  · simpa [z, positivePair] using hw

theorem blockSum_cuntzBelow {a b c d : Positive A} (hac : CuntzBelow a c) (hbd : CuntzBelow b d) :
    CuntzBelow (blockSum a b) (blockSum c d) :=
  CuntzBelow.map (diagonalTwo (A := A)) (positivePair_cuntzBelow hac hbd)

namespace CuntzClass

def blockAdd (x y : CuntzClass A) : CuntzClass (CStarMatrix (Fin 2) (Fin 2) A) :=
  Quotient.lift₂ (fun a b => mk (blockSum a b)) (fun (a b c d : Positive A) (hac : (cuntzSetoid A) a c) (hbd : (cuntzSetoid A) b d) =>
    (mk_eq_mk_iff _ _).mpr ⟨blockSum_cuntzBelow hac.1 hbd.1, blockSum_cuntzBelow hac.2 hbd.2⟩) x y
@[simp] lemma blockAdd_mk (a b : Positive A) : blockAdd (mk a) (mk b) = mk (blockSum a b) := rfl
lemma blockAdd_mono {x y u v : CuntzClass A} (hxu : x ≤ u) (hyv : y ≤ v) :
    blockAdd x y ≤ blockAdd u v := by
  induction x using Quotient.inductionOn with | h a =>
  induction y using Quotient.inductionOn with | h b =>
  induction u using Quotient.inductionOn with | h c =>
  induction v using Quotient.inductionOn with | h d =>
  exact blockSum_cuntzBelow hxu hyv
end CuntzClass

theorem ExtendedTrace.cuntzRank_blockAdd (τ : ExtendedTrace A) (x y : CuntzClass A) :
    (τ.matrixTrace (Fin 2)).cuntzRank (CuntzClass.blockAdd x y) = τ.cuntzRank x + τ.cuntzRank y := by
  induction x using Quotient.inductionOn with | h a =>
  induction y using Quotient.inductionOn with | h b =>
  exact blockSum_rank τ a b
end CuntzTrace

end

end OAI
