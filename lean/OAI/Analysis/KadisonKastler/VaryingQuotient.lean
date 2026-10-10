import OAI.Analysis.KadisonKastler.VaryingSequence
import OAI.Analysis.KadisonKastler.UltrapowerExpectation

namespace OAI

/-! # Trace-preserving embeddings of varying tracial products

Coordinate embeddings descend to the represented tracial quotients.
Faithfulness and the trace ultralimit formula supply the kernel inclusion;
no additional ultraproduct embedding principle is assumed.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

section Descent

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
variable (f : A →⋆ₐ[ℂ] B) (hf : Function.Surjective f) (g : A →⋆ₐ[ℂ] C)
variable (hker : ∀ x, f x = 0 → g x = 0)

include hker

private theorem descent_eq {x y : A} (hxy : f x = f y) : g x = g y := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hker
  rw [map_sub, hxy, sub_self]

private def descentValue (x : B) : C := g (Classical.choose (hf x))

private theorem descentValue_map (x : A) : descentValue f hf g (f x) = g x := by
  apply descent_eq f g hker
  exact Classical.choose_spec (hf (f x))

/-- Descent through a surjective star homomorphism with smaller kernel. -/
def starAlgHomDescend : B →⋆ₐ[ℂ] C where
  toFun := descentValue f hf g
  map_one' := by
    rw [← map_one f, descentValue_map f hf g hker, map_one]
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← map_mul, descentValue_map f hf g hker, map_mul,
      descentValue_map f hf g hker, descentValue_map f hf g hker]
  map_zero' := by
    rw [← map_zero f, descentValue_map f hf g hker, map_zero]
  map_add' x y := by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← map_add, descentValue_map f hf g hker, map_add,
      descentValue_map f hf g hker, descentValue_map f hf g hker]
  commutes' z := by
    calc
      descentValue f hf g (algebraMap ℂ B z) =
          descentValue f hf g (f (algebraMap ℂ A z)) :=
        congrArg (descentValue f hf g) (f.commutes z).symm
      _ = g (algebraMap ℂ A z) := descentValue_map f hf g hker _
      _ = algebraMap ℂ C z := g.commutes z
  map_star' x := by
    obtain ⟨a, rfl⟩ := hf x
    rw [← map_star, descentValue_map f hf g hker, map_star,
      descentValue_map f hf g hker]

@[simp]
theorem starAlgHomDescend_apply_map (x : A) :
    starAlgHomDescend f hf g hker (f x) = g x := descentValue_map f hf g hker x

end Descent

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
variable {C A D : Type*} [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra D]

/-- The quotient and its canonical trace formula for a varying product. -/
structure VaryingTraceQuotient (τ : ∀ j, FaithfulTracialState (B j))
    (σ : FaithfulTracialState C) (ω : Ultrafilter ℕ) where
  quotient : VaryingBoundedSequence B →⋆ₐ[ℂ] C
  surjective : Function.Surjective quotient
  trace_limit : ∀ s, Tendsto (fun j => (τ j).toLinearMap (s j)) (ω : Filter ℕ)
    (𝓝 (σ.toLinearMap (quotient s)))

namespace VaryingTraceQuotient

variable {τ : ∀ j, FaithfulTracialState (B j)} {σ : FaithfulTracialState C}
variable {τA : FaithfulTracialState A} {σD : FaithfulTracialState D} {ω : Ultrafilter ℕ}
variable (Q : VaryingTraceQuotient τ σ ω) (R : TraceQuotientMap τA σD ω)
variable (φ : ∀ j, B j →⋆ₐ[ℂ] A)
variable (hφ : ∀ j x, τA.toLinearMap (φ j x) = (τ j).toLinearMap x)

include hφ

/-- Coordinate trace preservation gives trace preservation before descent. -/
theorem mapped_trace (s : VaryingBoundedSequence B) :
    σD.toLinearMap (R.quotient (varyingSequenceMap φ s)) =
      σ.toLinearMap (Q.quotient s) := by
  have h := R.trace_limit (varyingSequenceMap φ s)
  simp only [varyingSequenceMap_apply, hφ] at h
  exact tendsto_nhds_unique h (Q.trace_limit s)

/-- Faithfulness gives the kernel inclusion for the induced map. -/
theorem mapped_zero (s : VaryingBoundedSequence B) (hs : Q.quotient s = 0) :
    R.quotient (varyingSequenceMap φ s) = 0 := by
  apply σD.faithful
  rw [← map_star, ← map_mul, ← map_star, ← map_mul,
    Q.mapped_trace R φ hφ, map_mul, map_star, hs, star_zero, zero_mul, map_zero]

/-- The trace-preserving embedding induced by the coordinate embeddings. -/
def inducedMap : C →⋆ₐ[ℂ] D :=
  starAlgHomDescend Q.quotient Q.surjective
    (R.quotient.comp (varyingSequenceMap φ)) (Q.mapped_zero R φ hφ)

@[simp]
theorem inducedMap_quotient (s : VaryingBoundedSequence B) :
    Q.inducedMap R φ hφ (Q.quotient s) = R.quotient (varyingSequenceMap φ s) :=
  starAlgHomDescend_apply_map _ _ _ _ s

theorem trace_inducedMap (x : C) :
    σD.toLinearMap (Q.inducedMap R φ hφ x) = σ.toLinearMap x := by
  obtain ⟨s, rfl⟩ := Q.surjective x
  rw [Q.inducedMap_quotient R φ hφ]
  exact Q.mapped_trace R φ hφ s

theorem inducedMap_injective : Function.Injective (Q.inducedMap R φ hφ) :=
  injective_of_trace_preserving σ σD _ (Q.trace_inducedMap R φ hφ)

end VaryingTraceQuotient

end

end KadisonKastler

end OAI
