import OAI.Analysis.KadisonKastler.RestrictedInnerDerivation
import OAI.Analysis.KadisonKastler.NormUltraproductMaps
import OAI.Analysis.KadisonKastler.UniformNormDetection

namespace OAI

/-! # Innerness in the norm ultraproduct gives uniform commutator control

This proves the analytic core of the infinitesimal-normalizer contradiction.
The hypotheses are simplicity of the type III ultraproduct and invariance
under the commutator.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u v

variable {A : Type u} {E : Type v} [CStarAlgebra A] [CStarAlgebra E]

/-- A spatial commutator along a star representation, as a bounded map. -/
def commutatorAlong (φ : A →⋆ₐ[ℂ] E) (T : E) : A →L[ℂ] E :=
  ((ContinuousLinearMap.mul ℂ E T - (ContinuousLinearMap.mul ℂ E).flip T)).comp
    (φ.toLinearMap.mkContinuous 1 (fun x => by
      change ‖φ x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ x))

@[simp] theorem commutatorAlong_apply (φ : A →⋆ₐ[ℂ] E) (T : E) (x : A) :
    commutatorAlong φ T x = T * φ x - φ x * T := rfl

variable {B : ℕ → Type u} {C : ℕ → Type v}
  [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  [∀ j, CStarAlgebra (C j)] [∀ j, Nontrivial (C j)]

theorem normUltraproduct_commutator_in_range
    (φ : ∀ j, B j →⋆ₐ[ℂ] C j) (ω : Ultrafilter ℕ)
    (T : VaryingBoundedSequence C)
    (hrange : ∀ x : VaryingBoundedSequence B,
      ∃ y : VaryingBoundedSequence B,
        NormNullSequence C ω (T * normProductMap φ x - normProductMap φ x * T -
          normProductMap φ y)) :
    ∀ x : NormUltraproduct B ω, ∃ y : NormUltraproduct B ω,
      normUltraproductInducedMap φ ω y =
        normUltraproductMap C ω T * normUltraproductInducedMap φ ω x -
          normUltraproductInducedMap φ ω x * normUltraproductMap C ω T := by
  intro x
  obtain ⟨X, rfl⟩ := normUltraproductMap_surjective B ω x
  obtain ⟨Y, hY⟩ := hrange X
  refine ⟨normUltraproductMap B ω Y, ?_⟩
  have hzero := (normUltraproductMap_eq_zero_iff C ω _).mpr hY
  rw [map_sub, map_sub, map_mul, map_mul] at hzero
  simpa only [normUltraproductInducedMap_apply_map] using (sub_eq_zero.mp hzero).symm

/-- Equality of the two derivations gives a single bounded self-adjoint
coordinate correction whose commutator norms converge uniformly to zero. -/
theorem exists_uniform_commutator_correction
    (hPublished : PublishedSimpleDerivationInner.{u})
    (φ : ∀ j, B j →⋆ₐ[ℂ] C j) (hφ : ∀ j, Function.Injective (φ j))
    (ω : Ultrafilter ℕ) (hSimple : CStarSimple (NormUltraproduct B ω))
    (T : VaryingBoundedSequence C) (hT : IsSelfAdjoint T)
    (hrange : ∀ x : VaryingBoundedSequence B,
      ∃ y : VaryingBoundedSequence B,
        NormNullSequence C ω (T * normProductMap φ x - normProductMap φ x * T -
          normProductMap φ y)) :
    ∃ a : VaryingBoundedSequence B, IsSelfAdjoint a ∧
      Tendsto (fun j => ‖commutatorAlong (φ j) (T j - φ j (a j))‖)
        (ω : Filter ℕ) (𝓝 0) := by
  let Φ := normUltraproductInducedMap φ ω
  let t := normUltraproductMap C ω T
  have ht : IsSelfAdjoint t := by
    change star (normUltraproductMap C ω T) = normUltraproductMap C ω T
    rw [← map_star, hT.star_eq]
  obtain ⟨a, ha, hcomm⟩ := exists_selfAdjoint_ambient_correction hPublished hSimple Φ
    (normUltraproductInducedMap_injective φ hφ ω) t ht
    (normUltraproduct_commutator_in_range φ ω T hrange)
  obtain ⟨aSeq, haSeq, haLift⟩ := exists_selfAdjoint_normUltraproduct_lift B ω a ha
  refine ⟨aSeq, haSeq, ?_⟩
  apply tendsto_opNorm_zero_of_bounded_sequence_tests ω
  intro X
  have hnull : NormNullSequence C ω
      ((T - normProductMap φ aSeq) * normProductMap φ X -
        normProductMap φ X * (T - normProductMap φ aSeq)) := by
    apply (normUltraproductMap_eq_zero_iff C ω _).mp
    rw [map_sub, map_mul, map_mul, map_sub,
      ← normUltraproductInducedMap_apply_map,
      ← normUltraproductInducedMap_apply_map, haLift]
    exact sub_eq_zero.mpr (hcomm (normUltraproductMap B ω X)).eq
  exact hnull

end

end KadisonKastler

end OAI
