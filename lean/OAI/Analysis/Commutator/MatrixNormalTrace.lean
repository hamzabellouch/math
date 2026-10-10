import Mathlib
import OAI.Analysis.Commutator.MatrixAlgebraEquiv
import OAI.Analysis.Commutator.MatrixEntryWOT
import OAI.Analysis.Commutator.MatrixTraceFaithful
import OAI.Analysis.Commutator.NormalGNS

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder Topology

open ContinuousLinearMapWOT

namespace Kadison.OperatorAmplification

lemma equiv_star_mul {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]
    (e : B ≃⋆ₐ[ℂ] C) (x : B) : e (star x*x)=star (e x)*e x := by
  rw [map_mul,map_star]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

local instance : DecidableEq ι := Classical.decEq ι

variable (τ : M →ₚ[ℂ] ℂ)

def matrixTrace : matrixVonNeumann ι i₀ M →ₚ[ℂ] ℂ where
  toLinearMap := (MatrixGNS.trace (ι:=ι) τ).toLinearMap.comp
    (matrixEquiv ι i₀ M).symm.toStarAlgHom.toLinearMap
  monotone' := (MatrixGNS.trace (ι:=ι) τ).monotone.comp
    (OrderHomClass.monotone (matrixEquiv ι i₀ M).symm.toStarAlgHom)

lemma matrixTrace_equiv (X : CStarMatrix ι ι M) :
    matrixTrace ι i₀ M τ (matrixEquiv ι i₀ M X)=MatrixGNS.trace (ι:=ι) τ X := by
  change MatrixGNS.trace (ι:=ι) τ ((matrixEquiv ι i₀ M).symm (matrixEquiv ι i₀ M X))=_
  rw [StarAlgEquiv.symm_apply_apply]

lemma matrixTrace_apply (T : matrixVonNeumann ι i₀ M) :
    matrixTrace ι i₀ M τ T=(Fintype.card ι : ℂ)⁻¹ * ∑ i,
      τ ⟨entry ι (T:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i i,
        (mem_matrixVonNeumann ι i₀ M T).mp T.property i i⟩ := by
  change MatrixGNS.trace (ι:=ι) τ ((matrixEquiv ι i₀ M).symm T)=_
  rw [MatrixGNS.trace_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Subtype.ext
  exact matrixEquiv_symm_entry ι i₀ M T i i

lemma matrixTrace_one (h1 : τ 1=1) : matrixTrace ι i₀ M τ 1=1 := by
  let : Nonempty ι := ⟨i₀⟩
  change MatrixGNS.trace (ι:=ι) τ ((matrixEquiv ι i₀ M).symm 1)=1
  rw [map_one,MatrixGNS.trace_one τ h1]

lemma matrixTrace_tracial (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (X Y : matrixVonNeumann ι i₀ M) :
    matrixTrace ι i₀ M τ (X*Y)=matrixTrace ι i₀ M τ (Y*X) := by
  change MatrixGNS.trace (ι:=ι) τ ((matrixEquiv ι i₀ M).symm (X*Y))=
    MatrixGNS.trace (ι:=ι) τ ((matrixEquiv ι i₀ M).symm (Y*X))
  simp only [map_mul]
  exact MatrixGNS.trace_mul (ι:=ι) τ hτ _ _

lemma matrixTrace_faithful (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)
    (X : matrixVonNeumann ι i₀ M) (hX : matrixTrace ι i₀ M τ (star X*X)=0) : X=0 := by
  let : Nonempty ι := ⟨i₀⟩
  apply (matrixEquiv ι i₀ M).symm.injective
  rw [map_zero]
  apply MatrixGNS.trace_faithful (ι:=ι) τ hfaith
  change MatrixGNS.trace (ι:=ι) τ ((matrixEquiv ι i₀ M).symm (star X*X))=0 at hX
  rw [equiv_star_mul] at hX
  exact hX

lemma matrixTrace_normal (hnormal : NormalGNS.BoundedWOTContinuous M τ) :
    NormalGNS.BoundedWOTContinuous (matrixVonNeumann ι i₀ M) (matrixTrace ι i₀ M τ) := by
  intro C
  let F := {T : SumSpace (H:=H) ι →WOT[ℂ] SumSpace (H:=H) ι //
    T.toCLM∈matrixVonNeumann ι i₀ M ∧ ‖T.toCLM‖≤C}
  let f (i : ι) : F → {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} :=
    fun a => ⟨ofCLM (entry ι a.val.toCLM i i),
      (mem_matrixVonNeumann ι i₀ M a.val.toCLM).mp a.property.1 i i,
      (norm_entry_le ι a.val.toCLM i i).trans a.property.2⟩
  have hf (i : ι) : Continuous (f i) :=
    ((continuous_entryWOT ι i i).comp continuous_subtype_val).subtype_mk _
  have ht (i : ι) : Continuous (fun a : F => τ ⟨(f i a).val.toCLM,(f i a).property.1⟩) :=
    (hnormal C).comp (hf i)
  convert continuous_const.mul (continuous_finsetSum Finset.univ (fun i _ => ht i)) using 1
  ext a
  exact matrixTrace_apply ι i₀ M τ _

end Kadison.OperatorAmplification

end

end
end

end OAI
