import Mathlib
import OAI.Analysis.Commutator.FiniteHankel

namespace OAI

noncomputable section

section

noncomputable section

open ContinuousLinearMap

namespace Kadison.FreeCorner

variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

lemma isometry_adjoint_apply (F : K →ₗᵢ[ℂ] H) (x : K) :
    F.toContinuousLinearMap.adjoint (F x)=x :=
  congrArg (fun T : K →L[ℂ] K => T x) F.adjoint_comp_self

omit [CompleteSpace L] in
lemma isometry_project_range (E : L →ₗᵢ[ℂ] H) (F : K →ₗᵢ[ℂ] H)
    (hEF : Set.range E⊆Set.range F) (x : L) :
    F (F.toContinuousLinearMap.adjoint (E x))=E x := by
  obtain ⟨y,hy⟩ := hEF (Set.mem_range_self x)
  rw [←hy,isometry_adjoint_apply]

def factorIsometry (E : L →ₗᵢ[ℂ] H) (F : K →ₗᵢ[ℂ] H)
    (hEF : Set.range E⊆Set.range F) : L →ₗᵢ[ℂ] K where
  toLinearMap := (F.toContinuousLinearMap.adjoint.comp E.toContinuousLinearMap).toLinearMap
  norm_map' x := by
    change ‖F.toContinuousLinearMap.adjoint (E x)‖=‖x‖
    rw [←F.norm_map,isometry_project_range E F hEF,E.norm_map]

omit [CompleteSpace L] in
lemma factorIsometry_comp (E : L →ₗᵢ[ℂ] H) (F : K →ₗᵢ[ℂ] H)
    (hEF : Set.range E⊆Set.range F) :
    F.toContinuousLinearMap.comp (factorIsometry E F hEF).toContinuousLinearMap=
      E.toContinuousLinearMap := by
  ext x
  exact isometry_project_range E F hEF x

lemma compress_factorIsometry (E : L →ₗᵢ[ℂ] H) (F : K →ₗᵢ[ℂ] H)
    (hEF : Set.range E⊆Set.range F) (T : H →L[ℂ] H) :
    compress E T=compress (factorIsometry E F hEF) (compress F T) := by
  have he := factorIsometry_comp E F hEF
  conv_lhs => rw [compress,←he,adjoint_comp]
  simp only [compress,comp_assoc]

lemma norm_compress_le_of_range_subset (E : L →ₗᵢ[ℂ] H) (F : K →ₗᵢ[ℂ] H)
    (hEF : Set.range E⊆Set.range F) (T : H →L[ℂ] H) :
    ‖compress E T‖≤‖compress F T‖ := by
  rw [compress_factorIsometry E F hEF T]
  exact norm_compress_le _ _

end Kadison.FreeCorner

end

end
end

end OAI
