import OAI.Analysis.KadisonKastler.TracialQuotientDiffuse

namespace OAI

/-! # The constant algebra inside its tracial sequence quotient -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

def boundedToVarying : BoundedSequence A →⋆ₐ[ℂ] VaryingBoundedSequence (fun _ => A) where
  toFun x := ⟨fun j => x j, memℓp_infty ⟨‖x‖, by rintro _ ⟨j, rfl⟩; exact x.norm_coe_le_norm j⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem boundedToVarying_surjective : Function.Surjective (boundedToVarying (A := A)) := by
  intro x
  refine ⟨varyingSequenceMap (fun _ => StarAlgHom.id ℂ A) x, ?_⟩
  apply Subtype.ext
  funext j
  rfl

def constantVarying : A →⋆ₐ[ℂ] VaryingBoundedSequence (fun _ => A) where
  toFun a := ⟨fun _ => a, memℓp_infty ⟨‖a‖, by rintro _ ⟨j, rfl⟩; exact le_rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def tracialConstantEmbedding (σ : FaithfulTracialState A) (ω : Ultrafilter ℕ) :
    A →⋆ₐ[ℂ] TracialSequenceQuotient (fun _ => σ) ω :=
  (tracialSequenceQuotientMap (fun _ => σ) ω).comp constantVarying

theorem tracialConstantEmbedding_injective (σ : FaithfulTracialState A) (ω : Ultrafilter ℕ) :
    Function.Injective (tracialConstantEmbedding σ ω) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have ht := (tracialSequenceQuotientMap_eq_zero_iff (fun _ => σ) ω
    (constantVarying (A := A) a)).mp ha
  change Tendsto (fun _ : ℕ => traceTwoNorm σ a) (ω : Filter ℕ) (𝓝 0) at ht
  exact (traceTwoNorm_eq_zero_iff σ a).mp (tendsto_nhds_unique tendsto_const_nhds ht)

theorem tracialConstantQuotient_infinite (σ : FaithfulTracialState A) (ω : Ultrafilter ℕ)
    (hA : ¬ FiniteDimensional ℂ A) :
    ¬ FiniteDimensional ℂ (TracialSequenceQuotient (fun _ => σ) ω) := by
  intro h
  let := h
  exact hA (FiniteDimensional.of_injective (tracialConstantEmbedding σ ω).toLinearMap
    (tracialConstantEmbedding_injective σ ω))

end

end KadisonKastler

end OAI
