import OAI.Analysis.KadisonSimilarity.Representation.SeparableRepresentationTests
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Instances.RealVectorSpace

namespace OAI

/-! # Extending the pointwise algebra in a fiber

This is the norm-continuity step in Blackadar, III.5.1.11. A contractive
unital ring representation on a dense subring extends to the C-star algebra.
Preservation of star and of `i · 1` makes that extension a complex star
representation. Countability is needed only to gather almost-everywhere
relations on a common conull set, not for the extension itself.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology CStarAlgebra

variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem denseSubring_uniformContinuous
    (S : Subring A) (f : S →+* (H →L[ℂ] H))
    (hnorm : ∀ a : S, ‖f a‖ ≤ ‖a‖) : UniformContinuous f := by
  apply (AddMonoidHomClass.lipschitz_of_bound f 1 ?_).uniformContinuous
  intro a
  simpa only [one_mul] using hnorm a

/-- The uniform extension, retaining its ring structure. -/
def denseSubringRepresentation (S : Subring A) (hdense : Dense (S : Set A))
    (f : S →+* (H →L[ℂ] H)) (hnorm : ∀ a : S, ‖f a‖ ≤ ‖a‖) :
    A →+* (H →L[ℂ] H) :=
  IsDenseInducing.extendRingHom (i := S.subtype)
    isUniformEmbedding_subtype_val.isUniformInducing hdense.denseRange_val
    (denseSubring_uniformContinuous S f hnorm)

theorem denseSubringRepresentation_continuous
    (S : Subring A) (hdense : Dense (S : Set A))
    (f : S →+* (H →L[ℂ] H)) (hnorm : ∀ a : S, ‖f a‖ ≤ ‖a‖) :
    Continuous (denseSubringRepresentation S hdense f hnorm) := by
  exact (uniformContinuous_uniformly_extend
    isUniformEmbedding_subtype_val.isUniformInducing hdense.denseRange_val
    (denseSubring_uniformContinuous S f hnorm)).continuous

@[simp] theorem denseSubringRepresentation_apply
    (S : Subring A) (hdense : Dense (S : Set A))
    (f : S →+* (H →L[ℂ] H)) (hnorm : ∀ a : S, ‖f a‖ ≤ ‖a‖) (a : S) :
    denseSubringRepresentation S hdense f hnorm a = f a :=
  IsDenseInducing.extend_eq
    (isUniformEmbedding_subtype_val.isUniformInducing.isDenseInducing hdense.denseRange_val)
    (denseSubring_uniformContinuous S f hnorm).continuous a

omit [CompleteSpace H] in
/-- Continuity of an additive map gives real linearity; preserving `i · 1`
then forces preservation of every complex scalar. -/
theorem continuousRingHom_commutes_complex
    (F : A →+* (H →L[ℂ] H)) (hF : Continuous F)
    (hI : F (algebraMap ℂ A Complex.I) = algebraMap ℂ (H →L[ℂ] H) Complex.I) :
    ∀ z : ℂ, F (algebraMap ℂ A z) = algebraMap ℂ (H →L[ℂ] H) z := by
  have hr (r : ℝ) : F (algebraMap ℂ A (r : ℂ)) =
      algebraMap ℂ (H →L[ℂ] H) (r : ℂ) := by
    calc
      F (algebraMap ℂ A (r : ℂ)) = F (r • (1 : A)) := by
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), Algebra.algebraMap_eq_smul_one]
        rfl
      _ = r • F 1 := map_real_smul F hF r 1
      _ = algebraMap ℂ (H →L[ℂ] H) (r : ℂ) := by
        rw [map_one, RCLike.real_smul_eq_coe_smul (K := ℂ),
          Algebra.algebraMap_eq_smul_one]
        rfl
  intro z
  calc
    F (algebraMap ℂ A z) =
        F (algebraMap ℂ A ((z.re : ℂ) + (z.im : ℂ) * Complex.I)) := by
      rw [Complex.re_add_im]
    _ = algebraMap ℂ (H →L[ℂ] H) ((z.re : ℂ) + (z.im : ℂ) * Complex.I) := by
      simp only [map_add, map_mul, hr, hI]
    _ = algebraMap ℂ (H →L[ℂ] H) z := by rw [Complex.re_add_im]

/-- A continuous ring extension is a complex star representation when its
dense restriction preserves star and the scalar `i`. -/
theorem exists_starRepresentation_of_ring_extension
    (S : Subring A) (hdense : Dense (S : Set A))
    (hstarS : ∀ a ∈ S, star a ∈ S) (hIS : algebraMap ℂ A Complex.I ∈ S)
    (f : S →+* (H →L[ℂ] H)) (F : A →+* (H →L[ℂ] H))
    (hF : Continuous F) (hext : ∀ a : S, F a = f a)
    (hstar : ∀ a : S, f ⟨star a.val, hstarS a.val a.property⟩ = star (f a))
    (hI : f ⟨algebraMap ℂ A Complex.I, hIS⟩ = algebraMap ℂ (H →L[ℂ] H) Complex.I) :
    ∃ σ : A →⋆ₐ[ℂ] (H →L[ℂ] H), ∀ a : S, σ a = f a := by
  have hFstar : ∀ a : A, F (star a) = star (F a) := by
    intro a
    refine hdense.denseRange_val.induction_on
      (p := fun a => F (star a) = star (F a)) a
      (isClosed_eq (hF.comp continuous_star) (continuous_star.comp hF)) ?_
    intro b
    calc
      F (star (b : A)) = f ⟨star b.val, hstarS b.val b.property⟩ :=
        hext ⟨star b.val, hstarS b.val b.property⟩
      _ = star (f b) := hstar b
      _ = star (F (b : A)) :=
        congrArg star (hext b).symm
  have hFI : F (algebraMap ℂ A Complex.I) = algebraMap ℂ (H →L[ℂ] H) Complex.I := by
    exact (hext ⟨algebraMap ℂ A Complex.I, hIS⟩).trans hI
  let σ : A →⋆ₐ[ℂ] (H →L[ℂ] H) := {
    F with
    commutes' := continuousRingHom_commutes_complex F hF hFI
    map_star' := hFstar }
  exact ⟨σ, hext⟩

/-- A contractive unital ring representation on a dense star subring extends
to a complex star representation when it preserves the scalar `i`. -/
theorem exists_starRepresentation_of_dense_subring
    (S : Subring A) (hdense : Dense (S : Set A))
    (hstarS : ∀ a ∈ S, star a ∈ S) (hIS : algebraMap ℂ A Complex.I ∈ S)
    (f : S →+* (H →L[ℂ] H)) (hnorm : ∀ a : S, ‖f a‖ ≤ ‖a‖)
    (hstar : ∀ a : S, f ⟨star a.val, hstarS a.val a.property⟩ = star (f a))
    (hI : f ⟨algebraMap ℂ A Complex.I, hIS⟩ = algebraMap ℂ (H →L[ℂ] H) Complex.I) :
    ∃ σ : A →⋆ₐ[ℂ] (H →L[ℂ] H), ∀ a : S, σ a = f a :=
  exists_starRepresentation_of_ring_extension S hdense hstarS hIS f
    (denseSubringRepresentation S hdense f hnorm)
    (denseSubringRepresentation_continuous S hdense f hnorm)
    (denseSubringRepresentation_apply S hdense f hnorm) hstar hI

/-- An extension from a norm-dense subring is unique. -/
theorem starRepresentation_ext_dense_subring
    (S : Subring A) (hdense : Dense (S : Set A))
    (σ ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : ∀ a : S, σ a = ρ a) : σ = ρ := by
  apply DFunLike.coe_injective
  exact hdense.denseRange_val.equalizer (map_continuous σ) (map_continuous ρ)
    (funext h)

end KadisonSimilarity

end

end OAI
