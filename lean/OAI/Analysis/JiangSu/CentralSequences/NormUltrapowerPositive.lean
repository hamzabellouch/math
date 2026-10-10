import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerBasic
import OAI.Analysis.JiangSu.CStarAlgebras.PositiveContractionLift

namespace OAI

section

noncomputable section
open scoped ENNReal

namespace NormUltra
variable {A : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)] {U : Ultrafilter ℕ}
namespace QuotientAlgebra
instance : PartialOrder (QuotientAlgebra A U) := CStarAlgebra.spectralOrder _
instance : StarOrderedRing (QuotientAlgebra A U) := CStarAlgebra.spectralOrderedRing _

theorem positive_contraction_representative [∀ n, PartialOrder (A n)]
    [∀ n, StarOrderedRing (A n)] {e : QuotientAlgebra A U}
    (hep : 0≤e) (hen : ‖e‖≤1) :
    ∃ x : BoundedFamilies A, mk U x=e ∧ (∀ n, 0≤x n) ∧ (∀ n, ‖x n‖≤1) := by
  let : PartialOrder (BoundedFamilies A) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (BoundedFamilies A) := CStarAlgebra.spectralOrderedRing _
  obtain ⟨x,hx,hxp,hxn⟩ := CStarLift.exists_positive_contraction (mkHom (A := A) (U := U))
    mk_surjective hep hen
  refine ⟨x,hx,?_,fun n => (BoundedFamilies.norm_coordinate_le x n).trans hxn⟩
  intro n
  let ev : BoundedFamilies A →⋆ₙₐ[ℂ] A n := {
    toFun := fun x : BoundedFamilies A => x n
    map_zero' := rfl
    map_add' _ _ := rfl
    map_mul' _ _ := rfl
    map_smul' _ _ := rfl
    map_star' _ := rfl }
  exact map_nonneg ev hxp

end QuotientAlgebra
end NormUltra

end
end

end OAI
