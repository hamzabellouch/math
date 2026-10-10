import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupScalarProduct
import OAI.Analysis.Pureness.Operators.UnitaryGroupGeneratedAlgebra

namespace OAI
noncomputable section
namespace CuntzPureness
local instance reducedFreeGroupUltraEmbeddingPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
open CuntzTrace Filter
open scoped ComplexOrder

abbrev FreeGroupUltraGenerated := unitaryGroupAlgebra freeGroupScalarUltraUnitary

def freeGroupUltraGeneratedTrace : TracialState FreeGroupUltraGenerated :=
  unitaryGroupTracialState freeGroupScalarUltraUnitary
    (scalarMatrixUltraTracialState freeGroupScalarUltrafilter)

lemma freeGroupUltraGeneratedTrace_delta (g : FreeGroup ℕ) :
    freeGroupUltraGeneratedTrace.functional (unitaryGroupGenerator freeGroupScalarUltraUnitary g) =
      if g=1 then 1 else 0 := freeGroupScalarUltraUnitary_trace g

lemma freeGroupUltraGeneratedTrace_faithful (a : FreeGroupUltraGenerated)
    (ha : freeGroupUltraGeneratedTrace.functional (star a*a)=0) : a=0 :=
  unitaryGroupTracialState_faithful freeGroupScalarUltraUnitary
    (scalarMatrixUltraTracialState freeGroupScalarUltrafilter)
    (fun a => (scalarMatrixUltraTracialState_faithful freeGroupScalarUltrafilter a).mp) a ha

def freeGroupUltraReducedEquiv : FreeGroupUltraGenerated ≃⋆ₐ[ℂ] ReducedFreeGroup :=
  groupTraceReducedEquiv freeGroupUltraGeneratedTrace
    (unitaryGroupGenerator freeGroupScalarUltraUnitary)
    freeGroupUltraGeneratedTrace_delta (unitaryGroupGenerator_dense freeGroupScalarUltraUnitary)
    freeGroupUltraGeneratedTrace_faithful

def reducedFreeGroupUltraEmbedding : ReducedFreeGroup →⋆ₐ[ℂ]
    ScalarTracialMatrixUltraproduct freeGroupScalarUltrafilter :=
  (unitaryGroupAlgebra freeGroupScalarUltraUnitary).subtype.comp
    freeGroupUltraReducedEquiv.symm.toStarAlgHom

lemma reducedFreeGroupUltraEmbedding_injective : Function.Injective reducedFreeGroupUltraEmbedding :=
  Subtype.val_injective.comp freeGroupUltraReducedEquiv.symm.injective

lemma reducedFreeGroupUltraEmbedding_isometry : Isometry reducedFreeGroupUltraEmbedding :=
  NonUnitalStarAlgHom.isometry reducedFreeGroupUltraEmbedding.toNonUnitalStarAlgHom
    reducedFreeGroupUltraEmbedding_injective

lemma reducedFreeGroupUltraEmbedding_trace (a : ReducedFreeGroup) :
    (scalarMatrixUltraTracialState freeGroupScalarUltrafilter).functional
      (reducedFreeGroupUltraEmbedding a) = (reducedGroupTracialState (FreeGroup ℕ)).functional a := by
  have h := groupTraceReducedEquiv_trace freeGroupUltraGeneratedTrace
    (unitaryGroupGenerator freeGroupScalarUltraUnitary)
    freeGroupUltraGeneratedTrace_delta (unitaryGroupGenerator_dense freeGroupScalarUltraUnitary)
    freeGroupUltraGeneratedTrace_faithful (freeGroupUltraReducedEquiv.symm a)
  change (reducedGroupTracialState (FreeGroup ℕ)).functional
    (freeGroupUltraReducedEquiv (freeGroupUltraReducedEquiv.symm a)) =
      (scalarMatrixUltraTracialState freeGroupScalarUltrafilter).functional
        (reducedFreeGroupUltraEmbedding a) at h
  simpa using h.symm

lemma reducedFreeGroupUltraEmbedding_generator (g : FreeGroup ℕ) :
    reducedFreeGroupUltraEmbedding (reducedGroupUnitary (FreeGroup ℕ) g) =
      freeGroupScalarUltraUnitary g := by
  have h := groupTraceReducedEquiv_generator freeGroupUltraGeneratedTrace
    (unitaryGroupGenerator freeGroupScalarUltraUnitary)
    freeGroupUltraGeneratedTrace_delta (unitaryGroupGenerator_dense freeGroupScalarUltraUnitary)
    freeGroupUltraGeneratedTrace_faithful g
  change freeGroupUltraReducedEquiv (unitaryGroupGenerator freeGroupScalarUltraUnitary g) = _ at h
  rw [← h]
  change ((freeGroupUltraReducedEquiv.symm
    (freeGroupUltraReducedEquiv (unitaryGroupGenerator freeGroupScalarUltraUnitary g))) :
      ScalarTracialMatrixUltraproduct freeGroupScalarUltrafilter) = _
  simp only [StarAlgEquiv.symm_apply_apply]
  rfl

theorem reducedFreeGroup_exists_scalarUltraEmbedding :
    ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop ∧
      ∃ ρ : ReducedFreeGroup →⋆ₐ[ℂ] ScalarTracialMatrixUltraproduct U,
        Function.Injective ρ ∧ Isometry ρ ∧
        ∀ a : ReducedFreeGroup, (scalarMatrixUltraTracialState U).functional (ρ a) =
          (reducedGroupTracialState (FreeGroup ℕ)).functional a :=
  ⟨freeGroupScalarUltrafilter, freeGroupScalarUltrafilter_free,
    reducedFreeGroupUltraEmbedding, reducedFreeGroupUltraEmbedding_injective,
    reducedFreeGroupUltraEmbedding_isometry, reducedFreeGroupUltraEmbedding_trace⟩
end CuntzPureness

end

end OAI
