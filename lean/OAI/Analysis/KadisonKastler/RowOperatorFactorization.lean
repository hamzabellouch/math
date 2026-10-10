import OAI.Analysis.BoundedHochschild.CompletelyBoundedFactorization
import OAI.Analysis.KadisonKastler.RowVariance
import OAI.Analysis.KadisonKastler.CompleteConjugation

namespace OAI

/-! Operator factorizations and their exact behavior under finite row averages.
The representation is supplied by the proved Paulsen--Stinespring construction.
-/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace
open BoundedHochschild.KadisonRingrose

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance rowFactorOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance rowFactorStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance rowFactorOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance rowFactorOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

theorem exists_row_operator_factorization [Nontrivial H] {M : VonNeumannAlgebra H}
    (F : Algebra M →ₗ[ℂ] Algebra M) {c : ℝ} (hc : 0 < c)
    (hF : CompletelyBoundedBy F c) :
    Nonempty (OperatorFactorization (M.toStarSubalgebra.subtype.toAlgHom.toLinearMap.comp F) c) := by
  let e := M.toStarSubalgebra.subtype
  have he := injective_starAlgHom_completelyIsometric e Subtype.val_injective
  apply factorization_of_complete_bound _ hc
  intro n X
  change ‖CStarMatrix.mapₗ (e.toAlgHom.toLinearMap.comp F) X‖ ≤ c * ‖X‖
  have hcomp : CStarMatrix.mapₗ (e.toAlgHom.toLinearMap.comp F) X =
      CStarMatrix.mapₗ e.toAlgHom.toLinearMap (CStarMatrix.mapₗ F X) := by
    ext i j
    rfl
  rw [hcomp, he]
  exact hF n n X

def representationRowAverage {M : VonNeumannAlgebra H}
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (R : H →L[ℂ] K) : H →L[ℂ] K :=
  ∑ i, (π (r i)).comp (R.comp (star (r i) : H →L[ℂ] H))

theorem finiteRightAverage_operator_factorization {M : VonNeumannAlgebra H}
    (F : Algebra M →ₗ[ℂ] Algebra M)
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L R : H →L[ℂ] K)
    (hF : ∀ a, (F a : H →L[ℂ] H) = L.adjoint.comp ((π a).comp R))
    {ι : Type*} [Fintype ι] (r : ι → Algebra M) (a : Algebra M) :
    (finiteRightAverage r F a : H →L[ℂ] H) =
      L.adjoint.comp ((π a).comp (representationRowAverage π r R)) := by
  ext ξ
  have hsum : (finiteRightAverage r F a : H →L[ℂ] H) =
      ∑ i, (F (a * r i) : H →L[ℂ] H) * (star (r i) : H →L[ℂ] H) := by
    simp [finiteRightAverage_apply]
  rw [hsum]
  simp only [representationRowAverage, sum_apply, ContinuousLinearMap.comp_apply, map_sum,
    mul_apply_eq_comp]
  change (∑ i, (F (a * r i) : H →L[ℂ] H) ((star (r i) : H →L[ℂ] H) ξ)) = _
  simp_rw [hF, map_mul, ContinuousLinearMap.comp_apply, mul_apply_eq_comp]

theorem representationRowAverage_comp {M : VonNeumannAlgebra H}
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → Algebra M) (s : κ → Algebra M) (R : H →L[ℂ] K) :
    representationRowAverage π r (representationRowAverage π s R) =
      representationRowAverage π (fun ij : ι × κ => r ij.1 * s ij.2) R := by
  ext ξ
  simp only [representationRowAverage, sum_apply,
    ContinuousLinearMap.comp_apply, map_sum, Fintype.sum_prod_type, star_mul, map_mul,
    MulMemClass.coe_mul, mul_apply_eq_comp]

end

end KadisonKastler

end OAI
