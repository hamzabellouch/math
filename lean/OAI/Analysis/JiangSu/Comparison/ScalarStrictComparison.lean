import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.Corner

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem StrictComparison.scalar (hcmp : StrictComparison A) (a b : A)
    (ha : 0≤a) (hb : 0≤b) (hb0 : b≠0)
    (hgap : ∀ τ : TracialState A,normalizedRootRank τ a<normalizedRootRank τ b) :
    CuntzSubequiv a b := by
  let e := scalarFinOneEquiv (A := A)
  have he (x : A) : scalarCorner (A := A) (le_refl 1) x=e x := by
    simp only [scalarCorner_apply,corner_refl,e]
  have hM : CuntzSubequiv (e a) (e b) := by
    apply (cuntzSubequiv_completedMatrixInclude_iff A 1 _ _).mp
    apply hcmp _ _ (completedMatrixInclude_nonneg A 1 _ (map_nonneg e ha))
      (completedMatrixInclude_nonneg A 1 _ (map_nonneg e hb))
    · intro hz
      have hx := (completedMatrixInclude_isometry A 1).injective (hz.trans (map_zero _).symm)
      exact hb0 (e.injective (hx.trans (map_zero e).symm))
    · intro τ
      rw [completedRootRank_include τ 1 _ (map_nonneg e ha),
        completedRootRank_include τ 1 _ (map_nonneg e hb),←he a,←he b,
        matrixRank_scalarCorner τ _ a ha,matrixRank_scalarCorner τ _ b hb]
      exact hgap τ
  apply (cuntzSubequiv_iff_sequence _ _).mpr
  obtain ⟨v,hv⟩ := (cuntzSubequiv_iff_sequence _ _).mp hM
  refine ⟨fun n => e.symm (v n),?_⟩
  have ht := ((StarAlgEquiv.isometry e.symm).continuous.tendsto (e a)).comp hv
  simpa only [Function.comp_def,map_mul,map_star,StarAlgEquiv.symm_apply_apply] using ht

end DirectComparison

end
end

end OAI
