import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! The compactness transfer used to reconstruct global core values
from their compact coordinate localizations. -/
noncomputable section
open Set Topology
namespace CubicFirstMoment

theorem cubicThetaCompact_of_norm_domination
    {H K L : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    [NormedAddCommGroup L] [NormedSpace ℂ L] [CompleteSpace L]
    (A : H →L[ℂ] L) (B : H →L[ℂ] K) (hB : IsCompactOperator B)
    (hbound : ∃ C : ℝ, ∀ u, ‖A u‖≤C*‖B u‖) : IsCompactOperator A := by
  let V := B.toLinearMap.range.topologicalClosure
  let g : H →L[ℂ] V := B.codRestrict V
    (fun u => Submodule.le_topologicalClosure _ ⟨u,rfl⟩)
  have hd : DenseRange g := by
    intro v
    rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    have he : Subtype.val '' Set.range g=Set.range B := by
      ext y
      constructor
      · rintro ⟨w,⟨u,rfl⟩,rfl⟩
        exact ⟨u,rfl⟩
      · rintro ⟨u,rfl⟩
        exact ⟨g u,⟨u,rfl⟩,rfl⟩
    rw [he]
    exact v.property
  let T : V →L[ℂ] L := A.toLinearMap.extendOfNorm g.toLinearMap
  have hT (u : H) : T (g u)=A u :=
    LinearMap.extendOfNorm_eq hd hbound u
  have hg : IsCompactOperator g :=
    hB.codRestrict (V:=V) (fun u => Submodule.le_topologicalClosure B.toLinearMap.range ⟨u,rfl⟩)
      (Submodule.isClosed_topologicalClosure B.toLinearMap.range)
  have he : (A : H → L)=T ∘ g := funext (fun u => (hT u).symm)
  rw [he]
  exact hg.clm_comp T

end CubicFirstMoment

end

end OAI
