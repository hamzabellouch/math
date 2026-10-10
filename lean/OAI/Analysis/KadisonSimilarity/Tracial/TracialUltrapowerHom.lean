import OAI.Analysis.KadisonSimilarity.Tracial.TracialUltrapowerActions
import OAI.Analysis.KadisonSimilarity.Tracial.GNSTracialGeometry

namespace OAI

/-! Trace-preserving homomorphisms induce homomorphisms of the actual
tracial quotients. In particular this realizes Q^ω inside P^ω. -/

noncomputable section
namespace KadisonSimilarity

open HochschildUltrapower TracialUltrapower Filter
open scoped ComplexOrder Topology BoundedContinuousFunction

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Apply a star homomorphism at every coordinate of a bounded sequence. -/
def boundedSequenceStarHom (φ : A →⋆ₐ[ℂ] B) : (ℕ →ᵇ A) →⋆ₐ[ℂ] (ℕ →ᵇ B) where
  toFun x := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun i => φ (x i))
    ‖x‖ (fun i => (NonUnitalStarAlgHom.norm_apply_le φ (x i)).trans (x.norm_coe_le_norm i))
  map_one' := by ext i; exact map_one φ
  map_mul' x y := by ext i; exact map_mul φ (x i) (y i)
  map_zero' := by ext i; exact map_zero φ
  map_add' x y := by ext i; exact map_add φ (x i) (y i)
  commutes' c := by ext i; exact φ.commutes c
  map_star' x := by ext i; exact map_star φ (x i)

@[simp] theorem boundedSequenceStarHom_apply (φ : A →⋆ₐ[ℂ] B) (x : ℕ →ᵇ A) (i : ℕ) :
    boundedSequenceStarHom φ x i = φ (x i) := rfl

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

include hφ in
theorem boundedSequenceStarHom_null (x : ℕ →ᵇ A) (hx : x ∈ ideal τA hA ω trA) :
    boundedSequenceStarHom φ x ∈ ideal τB hB ω trB := by
  apply (mem_nullSubmodule _ _ _).mpr
  have hn (i : ℕ) : ‖τB.toPreGNS (φ (x i))‖ = ‖τA.toPreGNS (x i)‖ := by
    simpa only [gnsTracialVector_apply, UniformSpace.Completion.norm_coe] using
      gnsTracialHom_norm τA τB φ hφ (x i)
  have hx' : Tendsto (fun i => ‖τA.toPreGNS (x i)‖) (ω : Filter ℕ) (𝓝 0) :=
    (mem_nullSubmodule _ _ x).mp hx
  change Tendsto (fun i => ‖τB.toPreGNS (φ (x i))‖) (ω : Filter ℕ) (𝓝 0)
  simpa only [hn] using hx'

/-- The induced star homomorphism of tracial ultrapowers. -/
def tracialUltrapowerMap : Ultrapower τA hA ω trA →⋆ₐ[ℂ] Ultrapower τB hB ω trB where
  toAlgHom := Ideal.Quotient.liftₐ (ideal τA hA ω trA)
    ((quotientHom τB hB ω trB).comp (boundedSequenceStarHom φ)).toAlgHom (by
      intro x hx
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr
        (boundedSequenceStarHom_null τA τB hA hB ω trA trB φ hφ x hx))
  map_star' x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact map_star ((quotientHom τB hB ω trB).comp (boundedSequenceStarHom φ)) a

@[simp] theorem tracialUltrapowerMap_mk (x : ℕ →ᵇ A) :
    tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ (quotientHom τA hA ω trA x) =
      quotientHom τB hB ω trB (boundedSequenceStarHom φ x) := rfl

/-- The induced map preserves the actual quotient trace. -/
theorem tracialUltrapowerMap_trace (x : Ultrapower τA hA ω trA) :
    quotientTrace τB hB ω trB (tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ x) =
      quotientTrace τA hA ω trA x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change sequenceTrace τB ω (boundedSequenceStarHom φ a) = sequenceTrace τA ω a
  apply congrArg (limUnder (ω : Filter ℕ))
  funext i
  exact hφ (a i)

/-- Faithfulness of the quotient trace makes the induced map injective. -/
theorem tracialUltrapowerMap_injective :
    Function.Injective (tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply quotientTrace_faithful τA hA ω trA
  rw [← tracialUltrapowerMap_trace τA τB hA hB ω trA trB φ hφ,
    map_mul, map_star, map_sub, hxy, sub_self, star_zero, zero_mul, map_zero]

end KadisonSimilarity

end

end OAI
