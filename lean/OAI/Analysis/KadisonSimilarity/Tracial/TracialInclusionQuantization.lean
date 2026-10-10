import OAI.Analysis.KadisonSimilarity.Tracial.TracialInclusionModel
import OAI.Analysis.KadisonSimilarity.Tracial.RelativeMatrixQuantization

namespace OAI

/-! Relative local quantization in two abstract von Neumann algebras, through
one faithful normal representation of their given inclusion. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial UltrapowerBridge
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {φ : A →⋆ₐ[ℂ] B} {τ : B →ₚ[ℂ] ℂ}

namespace TracialInclusionModel
variable (F : TracialInclusionModel φ τ)

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] in
theorem source_factor
    (h : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • (1 : A)) :
    ∀ c : F.N.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1 := by
  intro c hc
  obtain ⟨b, rfl⟩ := F.sourceEquiv.surjective c
  have hb (a : A) : a * b = b * a := by
    apply F.sourceEquiv.injective
    change F.sourceEquiv (a * b) = F.sourceEquiv (b * a)
    rw [map_mul, map_mul]
    exact hc (F.sourceEquiv a)
  obtain ⟨z, rfl⟩ := h b hb
  refine ⟨z, ?_⟩
  change F.sourceEquiv (z • 1) = z • 1
  rw [map_smul, map_one]

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] in
theorem source_diffuse
    (h : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q) :
    ∀ p : F.N.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q := by
  intro p hp hp0
  let e := F.sourceEquiv
  obtain ⟨q, hq, hq0, hqp, hpq, hqp'⟩ := h (e.symm p) (hp.map e.symm)
    (fun hz => hp0 (by simpa only [map_zero, e.apply_symm_apply] using congrArg e hz))
  refine ⟨e q, hq.map e, ?_, ?_, ?_, ?_⟩
  · intro hz
    apply hq0
    apply e.injective
    change e q = e 0
    simpa only [map_zero] using hz
  · exact fun hz => hqp (by simpa only [e.symm_apply_apply] using congrArg e.symm hz)
  · simpa only [map_mul, e.apply_symm_apply] using congrArg e hpq
  · simpa only [map_mul, e.apply_symm_apply] using congrArg e hqp'

omit [PartialOrder A] [StarOrderedRing A] [StarOrderedRing B] in
theorem source_irreducible
    (h : ∀ c : B, (∀ a : A, φ a * c = c * φ a) → ∃ z : ℂ, c = z • 1) :
    ∀ c : F.M.toStarSubalgebra,
      (∀ a : F.N.toStarSubalgebra, coordinateInclusion F.le a * c =
        c * coordinateInclusion F.le a) → ∃ z : ℂ, c = z • 1 := by
  intro c hc
  obtain ⟨b, rfl⟩ := F.ambientEquiv.surjective c
  have hb (a : A) : φ a * b = b * φ a := by
    apply F.ambientEquiv.injective
    change F.ambientEquiv (φ a * b) = F.ambientEquiv (b * φ a)
    rw [map_mul, map_mul, ← F.compatible a]
    exact hc (F.sourceEquiv a)
  obtain ⟨z, rfl⟩ := h b hb
  refine ⟨z, ?_⟩
  change F.ambientEquiv (z • 1) = z • 1
  rw [map_smul, map_one]

include F in
omit [PartialOrder A] [StarOrderedRing A] in
/-- A centered ambient family has an arbitrarily small compression by a
nonzero projection in the original source algebra. -/
theorem exists_small_source_compression [Nontrivial A]
    (hfactor : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (hirr : ∀ c : B, (∀ a : A, φ a * c = c * φ a) → ∃ z : ℂ, c = z • 1)
    {I : Type*} [Fintype I] (x : I → B) (hx : ∀ i, τ (x i) = 0)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧ (τ (φ q)).re < η ∧
      ∀ i, ‖τ.toPreGNS (φ q * x i * φ q)‖ ^ 2 < δ * (τ (φ q)).re := by
  let : Nontrivial F.N.toStarSubalgebra := nontrivial_of_ne
    (F.sourceEquiv 0) (F.sourceEquiv 1)
    (fun h => zero_ne_one (F.sourceEquiv.injective h))
  obtain ⟨q, hq, hq0, ht, hc⟩ := exists_source_small_projection_of_diffuse
    F.representation F.le (F.source_factor hfactor) (F.source_diffuse hdiff)
    (F.source_irreducible hirr) (fun i => F.ambientEquiv (x i))
    (fun i => (F.trace_eq (x i)).trans (hx i)) hδ hη
  let r := F.sourceEquiv.symm q
  have he : F.ambientEquiv (φ r) = coordinateInclusion F.le q := by
    rw [← F.compatible, F.sourceEquiv.apply_symm_apply]
  have htrace : τ (φ r) = F.representation.trace (coordinateInclusion F.le q) := by
    rw [← F.trace_eq, he]
  refine ⟨r, hq.map F.sourceEquiv.symm, ?_, by rwa [htrace], ?_⟩
  · intro hr
    apply hq0
    have hh := congrArg F.sourceEquiv hr
    simpa only [r, F.sourceEquiv.apply_symm_apply, map_zero] using hh
  · intro i
    rw [htrace]
    have hn := preGNS_norm_map_eq τ
      (vectorPositiveFunctional F.M F.representation.vector)
      F.ambientEquiv.toStarAlgHom F.trace_eq (φ r * x i * φ r)
    change ‖(vectorPositiveFunctional F.M F.representation.vector).toPreGNS
      (F.ambientEquiv (φ r * x i * φ r))‖ = _ at hn
    rw [map_mul F.ambientEquiv, map_mul F.ambientEquiv, he] at hn
    rw [← hn]
    exact hc i

end TracialInclusionModel

/-- Apply relative quantization directly to the supplied normal traces. -/
theorem exists_relative_compression_of_predual
    [Nontrivial A]
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (eA : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (eB : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] B)
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    (hnA : BoundedHochschild.TraceInPredual eA τA)
    (hnB : BoundedHochschild.TraceInPredual eB τB)
    (h1B : τB 1 = 1) (htrB : ∀ a b, τB (a * b) = τB (b * a))
    (hfB : ∀ a, τB (star a * a) = 0 → a = 0)
    (ψ : A →⋆ₐ[ℂ] B) (hi : Function.Injective ψ)
    (ht : ∀ a, τB (ψ a) = τA a)
    (hfactor : ∀ c : A, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
    (hdiff : ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
    (hirr : ∀ c : B, (∀ a : A, ψ a * c = c * ψ a) → ∃ z : ℂ, c = z • 1)
    {I : Type*} [Fintype I] (x : I → B) (hx : ∀ i, τB (x i) = 0)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧ (τB (ψ q)).re < η ∧
      ∀ i, ‖τB.toPreGNS (ψ q * x i * ψ q)‖ ^ 2 < δ * (τB (ψ q)).re := by
  obtain ⟨F⟩ := exists_tracialInclusionModel eA eB τA τB hnA hnB h1B htrB hfB ψ hi ht
  exact F.exists_small_source_compression hfactor hdiff hirr x hx hδ hη

end KadisonSimilarity

end

end OAI
