import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.QuotientSurjective

namespace OAI

section

noncomputable section
namespace NonunitalGamma
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nonempty (NormalizedTrace A)] (U : Ultrafilter ℕ)
local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)

def quotientInclusion : A →⋆ₙₐ[ℂ] FamilyUltrapower T U :=
  (familyUltrapowerMap T U).toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)

@[simp] lemma quotientInclusion_apply (a : A) :
    quotientInclusion U a=familyUltrapowerMap T U (Unitization.inr a) := rfl

theorem limitTrace_restricts_normalized [CompactSpace (NormalizedTrace A)]
    (s : ℕ → NormalizedTrace A) : ∃ σ : NormalizedTrace A, ∀ a : A,
      (familyLimitTrace T U s).functional (quotientInclusion U a)=σ.functional a := by
  let F : Ultrafilter (NormalizedTrace A) := U.map s
  obtain ⟨σ,_hσ,hlim⟩ := isCompact_univ.ultrafilter_le_nhds F (by simp)
  have traceTendsto : Tendsto s (U : Filter ℕ) (𝓝 σ) := hlim
  refine ⟨σ,?_⟩
  intro a
  have evalTendsto := ((NormalizedTrace.continuous_eval a).tendsto σ).comp traceTendsto
  have hu := familyLimitTrace_constant_tendsto T U s (Unitization.inr a)
  change Tendsto (fun n => (s n).unitized.functional (Unitization.inr a)) (U : Filter ℕ)
    (𝓝 ((familyLimitTrace T U s).functional (quotientInclusion U a))) at hu
  simp only [NormalizedTrace.unitized_inr] at hu
  exact tendsto_nhds_unique hu evalTendsto

theorem nonunitalTwoNorm_limit (a : lp (fun _ : ℕ => A) ∞) :
    Tendsto (fun n => ⨆ τ : NormalizedTrace A,
      Real.sqrt (τ.functional (star (a n)*a n)).re) (U : Filter ℕ)
      (𝓝 (familyTwoNorm (familyLimitTrace T U) (sequenceQuotientMap (A := A) U a))) := by
  have h := familyTwoNorm_limitTrace_tendsto T U (boundedInr (A := A) a)
  simpa only [familyTwoNorm,traceTwoNorm,boundedInr_apply,←Unitization.inr_star,
    ←Unitization.inr_mul,NormalizedTrace.unitized_inr,sequenceQuotientMap_apply] using h

end NonunitalGamma

end
end

end OAI
