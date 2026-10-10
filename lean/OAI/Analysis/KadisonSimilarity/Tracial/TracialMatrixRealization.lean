import OAI.Analysis.KadisonSimilarity.Tensor.InvariantIntertwiners
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-!
# Matrix stages inside an actual tracial Hilbert representation

A trace-preserving matrix embedding supplies the normalized Hilbert--Schmidt
geometry, the corner left action, and the centered projection used by the
invariant-intertwiner argument. No invariant-theory conclusion is an input.
-/

noncomputable section
namespace KadisonSimilarity

variable {R E α : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [Fintype α] [DecidableEq α]

/-- The centered subspace is the orthogonal complement of the trace vector. -/
abbrev centeredSubspace (Ω : E) : Submodule ℂ E := (ℂ ∙ Ω)ᗮ

/-- Center a represented algebra vector by its actual orthogonal projection. -/
def tracialCenter (V : R →ₗ[ℂ] E) : R →ₗ[ℂ] centeredSubspace (V 1) :=
  (centeredSubspace (V 1)).orthogonalProjectionOnto.toLinearMap.comp V

omit [StarRing R] [CompleteSpace E] in
@[simp] theorem tracialCenter_apply (V : R →ₗ[ℂ] E) (a : R) :
    tracialCenter V a = (centeredSubspace (V 1)).orthogonalProjectionOnto (V a) := rfl

omit [StarRing R] [CompleteSpace E] in
/-- Centering is contractive in the represented Hilbert norm. -/
theorem norm_tracialCenter_le (V : R →ₗ[ℂ] E) (a : R) :
    ‖tracialCenter V a‖ ≤ ‖V a‖ :=
  (centeredSubspace (V 1)).norm_orthogonalProjectionOnto_apply_le (V a)

omit [StarRing R] [CompleteSpace E] in
@[simp] theorem tracialCenter_one (V : R →ₗ[ℂ] E) : tracialCenter V 1 = 0 :=
  Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero (V 1)

omit [StarRing R] [CompleteSpace E] in
/-- Density of the represented algebra passes to its centered projection. -/
theorem denseRange_tracialCenter (V : R →ₗ[ℂ] E) (hdense : DenseRange V) :
    DenseRange (tracialCenter V) := by
  have hs : Function.Surjective (centeredSubspace (V 1)).orthogonalProjectionOnto := by
    intro x
    exact ⟨x, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
  exact hs.denseRange.comp hdense
    (centeredSubspace (V 1)).orthogonalProjectionOnto.continuous

omit [StarRing R] [CompleteSpace E] in
/-- Subtracting the trace creates an algebraic trace-zero vector and does not
change its centered projection. -/
theorem tracialCenter_sub_trace (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (a : R) :
    tracialCenter V (a - τ a • 1) = tracialCenter V a := by
  simp only [map_sub, map_smul, tracialCenter_one, smul_zero, sub_zero]

omit [StarRing R] in
theorem trace_sub_trace (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1) (a : R) :
    τ (a - τ a • 1) = 0 := by
  simp only [map_sub, map_smul, hτ, smul_eq_mul, mul_one, sub_self]

omit [CompleteSpace E] in
/-- Trace-zero algebra vectors already lie in the centered subspace. -/
theorem tracial_vector_mem_centered (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E)
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (a : R) (ha : τ a = 0) : V a ∈ centeredSubspace (V 1) := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, hinner]
  simpa only [star_one, one_mul] using ha

omit [CompleteSpace E] in
/-- Inserting a centered trace-zero vector back into the full Hilbert space
recovers the original vector exactly. -/
theorem coe_tracialCenter_of_trace_zero (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E)
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (a : R) (ha : τ a = 0) : (tracialCenter V a : E) = V a := by
  exact (centeredSubspace (V 1)).starProjection_eq_self_iff.mpr
    (tracial_vector_mem_centered τ V hinner a ha)

omit [CompleteSpace E] in
/-- Orthogonal centering is precisely subtraction of the trace component. -/
theorem coe_tracialCenter (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E)
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b)) (hτ : τ 1 = 1)
    (a : R) : (tracialCenter V a : E) = V a - τ a • V 1 := by
  have h := coe_tracialCenter_of_trace_zero τ V hinner (a - τ a • 1)
    (trace_sub_trace τ hτ a)
  rw [tracialCenter_sub_trace] at h
  simpa only [map_sub, map_smul] using h

omit [CompleteSpace E] in
/-- A normalized trace gives the required unit trace vector. -/
theorem norm_tracialTraceVector (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E)
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b)) (hτ : τ 1 = 1) :
    ‖V 1‖ = 1 := by
  have hs : ‖V 1‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hinner, star_one, one_mul, hτ]
    rfl
  nlinarith [norm_nonneg (V 1)]

/-- The concrete normalized matrix stage associated to a trace-preserving
matrix star homomorphism and the left tracial representation. -/
def tracialMatrixStage
    (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] R)
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (htrace : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a) :
    MatrixHilbertStage (E := E) (F := centeredSubspace (V 1)) (α := α) where
  full := V.comp ι.toLinearMap
  center := (tracialCenter V).comp ι.toLinearMap
  left a := L (ι a)
  inner_full a b := by
    change inner ℂ (V (ι a)) (V (ι b)) = _
    rw [hinner, ← map_star, ← map_mul, htrace]
  norm_center_le a := norm_tracialCenter_le V (ι a)
  left_apply a b := by
    change L (ι a) (V (ι b)) = V (ι (a * b))
    rw [hleft, map_mul ι]
  left_adjoint a := by
    change star (L (ι a)) = L (ι (star a))
    rw [← map_star, ← map_star]

@[simp] theorem tracialMatrixStage_full
    (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] R) (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (htrace : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a) (a : Matrix α α ℂ) :
    (tracialMatrixStage τ V L ι hinner hleft htrace).full a = V (ι a) := rfl

@[simp] theorem tracialMatrixStage_unit
    (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] R) (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (htrace : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a) :
    (tracialMatrixStage τ V L ι hinner hleft htrace).full 1 = V 1 := by
  simp

/-- The stage centering acts as the identity on trace-zero matrices after
including its value in the full Hilbert space. -/
theorem coe_tracialMatrixStage_center_of_trace_zero
    (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] R) (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (htrace : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a)
    (a : Matrix α α ℂ) (ha : Matrix.trace a = 0) :
    ((tracialMatrixStage τ V L ι hinner hleft htrace).center a : E) = V (ι a) := by
  apply coe_tracialCenter_of_trace_zero τ V hinner
  change τ (ι a) = 0
  rw [htrace, ha, mul_zero]

/-- Thus the centered trace-zero matrix vectors have the actual normalized
Hilbert--Schmidt inner product. -/
theorem inner_tracialMatrixStage_center
    (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] R) (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (htrace : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a)
    (a b : Matrix α α ℂ) (ha : Matrix.trace a = 0) (hb : Matrix.trace b = 0) :
    inner ℂ ((tracialMatrixStage τ V L ι hinner hleft htrace).center a)
      ((tracialMatrixStage τ V L ι hinner hleft htrace).center b) =
      (Fintype.card α : ℂ)⁻¹ * Matrix.trace (star a * b) := by
  change inner ℂ (((tracialMatrixStage τ V L ι hinner hleft htrace).center a : E))
    (((tracialMatrixStage τ V L ι hinner hleft htrace).center b : E)) = _
  rw [coe_tracialMatrixStage_center_of_trace_zero τ V L ι hinner hleft htrace a ha,
    coe_tracialMatrixStage_center_of_trace_zero τ V L ι hinner hleft htrace b hb]
  exact (tracialMatrixStage τ V L ι hinner hleft htrace).inner_full a b

section Conjugation

variable [StarModule ℂ R]

variable (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E)
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (htrace : ∀ a b, τ (a * b) = τ (b * a))
  (hdense : DenseRange V)

include hinner htrace in
omit [CompleteSpace E] [StarModule ℂ R] in
/-- The tracial identity makes algebraic involution isometric in the represented
Hilbert norm, even before a norm on the algebra has been specified. -/
theorem norm_tracial_star (a : R) : ‖V (star a)‖ = ‖V a‖ := by
  have hs : ‖V (star a)‖ ^ 2 = ‖V a‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      hinner, hinner, star_star, htrace]
  nlinarith [norm_nonneg (V a), norm_nonneg (V (star a))]

/-- The actual tracial conjugation is obtained by extending algebraic involution
from the dense represented algebra. -/
def tracialConjugation : E →ₗᵢ⋆[ℂ] E :=
  (V.comp (starLinearEquiv ℂ).toLinearMap).extendOfIsometry
    (e := V) hdense (norm_tracial_star τ V hinner htrace)

@[simp] theorem tracialConjugation_apply_vector (a : R) :
    tracialConjugation τ V hinner htrace hdense (V a) = V (star a) := by
  exact LinearMap.extendOfIsometry_eq _ hdense
    (norm_tracial_star τ V hinner htrace) a

@[simp] theorem tracialConjugation_traceVector :
    tracialConjugation τ V hinner htrace hdense (V 1) = V 1 := by
  simp

/-- The dense extension remains an involution. -/
theorem tracialConjugation_involutive :
    Function.Involutive (tracialConjugation τ V hinner htrace hdense) := by
  intro x
  refine hdense.induction_on x (isClosed_eq (by fun_prop) continuous_id) ?_
  intro a
  simp

/-- Tracial conjugation reverses the Hilbert inner product. -/
theorem inner_tracialConjugation (x y : E) :
    inner ℂ (tracialConjugation τ V hinner htrace hdense x)
      (tracialConjugation τ V hinner htrace hdense y) = inner ℂ y x := by
  refine hdense.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro a b
  simp only [tracialConjugation_apply_vector, hinner, star_star]
  exact htrace a (star b)

/-- The trace-vector orthogonal complement is stable under actual tracial
conjugation. -/
theorem tracialConjugation_mem_centered (x : centeredSubspace (V 1)) :
    tracialConjugation τ V hinner htrace hdense x ∈ centeredSubspace (V 1) := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  calc
    inner ℂ (V 1) (tracialConjugation τ V hinner htrace hdense (x : E)) =
        inner ℂ (x : E) (V 1) := by
      simpa only [tracialConjugation_traceVector] using
        inner_tracialConjugation τ V hinner htrace hdense (V 1) (x : E)
    _ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.mp x.property

/-- Tracial conjugation restricted to the centered Hilbert space. -/
def centeredTracialConjugation :
    centeredSubspace (V 1) →ₗᵢ⋆[ℂ] centeredSubspace (V 1) where
  toFun x := ⟨tracialConjugation τ V hinner htrace hdense x,
    tracialConjugation_mem_centered τ V hinner htrace hdense x⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (tracialConjugation τ V hinner htrace hdense) (x : E) (y : E)
  map_smul' c x := by
    apply Subtype.ext
    exact (tracialConjugation τ V hinner htrace hdense).map_smulₛₗ c (x : E)
  norm_map' x := (tracialConjugation τ V hinner htrace hdense).norm_map x

@[simp] theorem coe_centeredTracialConjugation (x : centeredSubspace (V 1)) :
    (centeredTracialConjugation τ V hinner htrace hdense x : E) =
      tracialConjugation τ V hinner htrace hdense x := rfl

theorem centeredTracialConjugation_involutive :
    Function.Involutive (centeredTracialConjugation τ V hinner htrace hdense) := by
  intro x
  apply Subtype.ext
  exact tracialConjugation_involutive τ V hinner htrace hdense x

/-- The continuous bilinear pairing used for matrix trace contractions is built
from the actual centered tracial conjugation. -/
def centeredTracialPairing :
    centeredSubspace (V 1) →L[ℂ] centeredSubspace (V 1) →L[ℂ] ℂ :=
  (innerSL ℂ).comp
    (centeredTracialConjugation τ V hinner htrace hdense).toContinuousLinearMap

theorem centeredTracialPairing_conjugation (x y : centeredSubspace (V 1)) :
    centeredTracialPairing τ V hinner htrace hdense x
      (centeredTracialConjugation τ V hinner htrace hdense y) = inner ℂ y x := by
  exact inner_tracialConjugation τ V hinner htrace hdense x y

/-- On centered matrix vectors the pairing is exactly the normalized matrix
trace, without an assumed pairing formula. -/
theorem centeredTracialPairing_matrix
    (L : R →⋆ₐ[ℂ] (E →L[ℂ] E)) (ι : Matrix α α ℂ →⋆ₐ[ℂ] R)
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (hι : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a)
    (a b : Matrix α α ℂ) (ha : Matrix.trace a = 0) (hb : Matrix.trace b = 0) :
    centeredTracialPairing τ V hinner htrace hdense
      ((tracialMatrixStage τ V L ι hinner hleft hι).center a)
      ((tracialMatrixStage τ V L ι hinner hleft hι).center b) =
      (Fintype.card α : ℂ)⁻¹ * Matrix.trace (a * b) := by
  change inner ℂ
    (tracialConjugation τ V hinner htrace hdense
      (((tracialMatrixStage τ V L ι hinner hleft hι).center a : E)))
    (((tracialMatrixStage τ V L ι hinner hleft hι).center b : E)) = _
  rw [coe_tracialMatrixStage_center_of_trace_zero τ V L ι hinner hleft hι a ha,
    coe_tracialMatrixStage_center_of_trace_zero τ V L ι hinner hleft hι b hb,
    tracialConjugation_apply_vector, hinner, star_star, ← map_mul, hι]

end Conjugation

end KadisonSimilarity

end

end OAI
