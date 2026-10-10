import OAI.Analysis.Pureness.Completion.SharedMatrixBridge
import OAI.Analysis.Pureness.Stabilization.MatrixAdditionAssoc
import OAI.Analysis.Pureness.Cuntz.CuntzOrder

namespace OAI
open scoped CStarAlgebra
noncomputable section
namespace CuntzPureness
open CuntzTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem cuntzSubequiv_iff_shared {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (a b : Positive D) :
    CuntzSubequiv a.1 b.1 ↔ CuntzTrace.CuntzBelow a b := by
  rw [cuntzSubequiv_iff_norm]
  simp only [CuntzTrace.CuntzBelow, norm_sub_rev]

def completedSharedClass (a : Positive (CornerCompletion A)) :
    CuntzTrace.CuntzClass (CuntzTrace.MatrixLimit A) :=
  CuntzTrace.CuntzClass.mk (Positive.map sharedMatrixEquiv.symm.toNonUnitalStarAlgHom a)

lemma shared_positive_roundtrip (a : Positive (CornerCompletion A)) :
    Positive.map sharedMatrixEquiv.toNonUnitalStarAlgHom
      (Positive.map sharedMatrixEquiv.symm.toNonUnitalStarAlgHom a) = a := by
  apply Subtype.ext
  exact sharedMatrixEquiv.apply_symm_apply a.1

lemma shared_cuntz_map_equiv {D E : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] [NonUnitalCStarAlgebra E]
    [PartialOrder E] [StarOrderedRing E] (e : D ≃⋆ₐ[ℂ] E) (a b : Positive D) :
    CuntzTrace.CuntzBelow (Positive.map e.toNonUnitalStarAlgHom a)
      (Positive.map e.toNonUnitalStarAlgHom b) ↔ CuntzTrace.CuntzBelow a b := by
  constructor
  · intro h
    have hm := h.map e.symm.toNonUnitalStarAlgHom
    have ha : Positive.map e.symm.toNonUnitalStarAlgHom (Positive.map e.toNonUnitalStarAlgHom a) = a :=
      Subtype.ext (e.symm_apply_apply a.1)
    have hb : Positive.map e.symm.toNonUnitalStarAlgHom (Positive.map e.toNonUnitalStarAlgHom b) = b :=
      Subtype.ext (e.symm_apply_apply b.1)
    rwa [ha,hb] at hm
  · exact fun h => h.map e.toNonUnitalStarAlgHom

theorem completedSharedClass_le_iff (a b : Positive (CornerCompletion A)) :
    completedSharedClass a ≤ completedSharedClass b ↔ CuntzSubequiv a.1 b.1 := by
  unfold completedSharedClass
  rw [CuntzTrace.CuntzClass.mk_le_mk, shared_cuntz_map_equiv, cuntzSubequiv_iff_shared]

theorem completedSharedClass_surjective : Function.Surjective (completedSharedClass (A := A)) := by
  intro x
  induction x using Quotient.inductionOn with
  | h a =>
    refine ⟨Positive.map sharedMatrixEquiv.toNonUnitalStarAlgHom a, ?_⟩
    apply congrArg CuntzTrace.CuntzClass.mk
    apply Subtype.ext
    exact sharedMatrixEquiv.symm_apply_apply a.1

theorem shared_zero_sandwich (n : ℕ) :
    n • (0 : CuntzTrace.CuntzClass (CuntzTrace.MatrixLimit A)) ≤ 0 ∧
      (0 : CuntzTrace.CuntzClass (CuntzTrace.MatrixLimit A)) ≤ (n+1) • 0 := by
  simp
end CuntzPureness

end

end OAI
