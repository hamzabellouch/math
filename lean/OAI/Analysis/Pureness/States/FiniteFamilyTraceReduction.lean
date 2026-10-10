import OAI.Analysis.Pureness.States.FiniteFamilyMatrixCompletion
import OAI.Analysis.Pureness.States.FiniteFamilyExtremalCompletion
import OAI.Analysis.Pureness.States.QuotientFactorTrace
import OAI.Analysis.Pureness.Cuntz.FinOneMatrixTransport

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
namespace CompatibleFiniteQuasitrace
variable (F : CompatibleFiniteQuasitrace A)
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))

def originalEmbedding : A →⋆ₐ[ℂ] F.CauchyLevel hmono 0 :=
  (F.cauchyEmbedding hmono 0).comp (scalarMatrixHom (ι := Fin 1))

lemma cauchyValue_original (x : A) :
    F.cauchyValue hmono 0 (F.originalEmbedding hmono x)=F.toTwoQuasitrace.base x :=
  F.cauchyValue_embedding hmono 0 (scalarMatrixHom x)

lemma completedFamily_original (x : A) :
    (F.completedFamily hmono).toTwoQuasitrace.base (F.originalEmbedding hmono x)=F.toTwoQuasitrace.base x :=
  (F.completedFamily_base hmono _).trans (F.cauchyValue_original hmono x)

lemma originalEmbedding_cover (M : FinMatrix A 1) :
    ∃ a : A, F.originalEmbedding hmono a=F.cauchyEmbedding hmono 0 M := by
  obtain ⟨a,ha⟩ := scalarMatrixHom_finOne_bijective.2 M
  exact ⟨a,congrArg (F.cauchyEmbedding hmono 0) ha⟩

variable (hF : F.level 1 1=1)
variable (hext : F.toTwoQuasitrace.base.toFun ∈
  (normalizedFiniteBaseQuasitraceCarrier (A := A)).extremePoints ℝ)

include hF hext in

theorem extreme_cauchyLevel_central_projection (p : F.CauchyLevel hmono 0)
    (hp : IsStarProjection p) (hc : ∀ x, Commute p x) : p=0 ∨ p=1 := by
  apply (F.positiveLevel hmono 1).finiteFamily_faithful_extreme_completion_central_projection
    (F.positiveLevel_metricSize_add hmono 1) (F.positiveLevel_sqrt_add hmono 1)
    (F.completedFamily hmono) (F.completedFamily_monotone hmono) (F.completedFamily_unit hmono hF)
    1 (fun x => by rw [one_mul]; exact F.completedFamily_base hmono x)
    (F.originalEmbedding hmono) (F.originalEmbedding_cover hmono) _ _ p hp hc
  · simpa only [F.completedFamily_original] using hext
  · intro x
    rw [F.completedFamily_base]
    exact F.cauchyValue_faithful hmono 0 x

include hF hext in

theorem extreme_cauchy_trace_agrees (τ : TracialState (F.CauchyLevel hmono 0)) :
    ∀ x, τ.functional x=F.cauchyValue hmono 0 x := by
  have hunit : F.cauchyQuasitrace hmono 0 1=1 := by
    rw [F.cauchyQuasitrace_eq,← map_one (F.cauchyEmbedding hmono 0),F.cauchyValue_embedding,hF]
  have h := (F.positiveLevel hmono 1).quotient_factor_trace_agrees
    (F.positiveLevel_metricSize_add hmono 1) (F.positiveLevel_sqrt_add hmono 1)
    (F.extreme_cauchyLevel_central_projection hmono hF hext)
    (F.cauchyQuasitrace hmono 0) hunit 1
    (fun x => by rw [one_mul]; exact F.cauchyQuasitrace_eq hmono 0 x) τ
  simpa only [F.cauchyQuasitrace_eq] using h

include hF hext in
theorem extreme_original_additive_of_cauchy_trace (τ : TracialState (F.CauchyLevel hmono 0)) :
    ∀ a b, F.toTwoQuasitrace.base (a+b)=F.toTwoQuasitrace.base a+F.toTwoQuasitrace.base b := by
  have h := F.extreme_cauchy_trace_agrees hmono hF hext τ
  intro a b
  rw [← F.cauchyValue_original hmono,← F.cauchyValue_original hmono,
    ← F.cauchyValue_original hmono,← h,← h,← h,map_add,map_add]

end CompatibleFiniteQuasitrace

theorem finiteBase_extreme_additive_of_cauchy_traces
    (htrace : ∀ (F : CompatibleFiniteQuasitrace A)
      (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re)),
      F.level 1 1=1 → F.toTwoQuasitrace.base.toFun ∈
        (normalizedFiniteBaseQuasitraceCarrier (A := A)).extremePoints ℝ →
      Nonempty (TracialState (F.CauchyLevel hmono 0))) :
    (normalizedFiniteBaseQuasitraceCarrier (A := A)).extremePoints ℝ ⊆ additiveQuasitraceFunctions := by
  intro g hg
  obtain ⟨F,hmono,hF,rfl⟩ := (mem_normalizedFiniteBaseQuasitraceCarrier g).mp hg.1
  obtain ⟨τ⟩ := htrace F hmono hF hg
  exact F.extreme_original_additive_of_cauchy_trace hmono hF hg τ
end CuntzPureness

end

end OAI
