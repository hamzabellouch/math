import OAI.Analysis.KadisonSimilarity.Derivation.DiagonalMatrixNorm
import OAI.Analysis.KadisonSimilarity.Representation.SquareArrayPadding
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

namespace OAI

/-! # Reducing operator fields to their projection fibers

Each orthogonal projection has an actual closed Hilbert range. Compression
of a supported operator to this range preserves its norm and action. These
constructions are pointwise, so they apply to every fixed operator field;
no simultaneous representation law on an uncountable algebra is required.
-/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual closed range of an orthogonal projection. -/
def projectionFiber (p : H →L[ℂ] H) (hp : IsStarProjection p) : ClosedSubmodule ℂ H :=
  ⟨p.range, ContinuousLinearMap.IsIdempotentElem.isClosed_range hp.isIdempotentElem⟩

def projectionFiberInclusion (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    projectionFiber p hp →ₗᵢ[ℂ] H := (projectionFiber p hp).toSubmodule.subtypeₗᵢ

def projectionFiberRetraction (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    H →L[ℂ] projectionFiber p hp := p.codRestrict _ (fun x => ⟨x, rfl⟩)

@[simp] theorem projectionFiberRetraction_coe (p : H →L[ℂ] H) (hp : IsStarProjection p) (x : H) :
    (projectionFiberRetraction p hp x : H) = p x := rfl

theorem projectionFiber_fixed (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (x : projectionFiber p hp) : p (x : H) = x := by
  obtain ⟨y, hy⟩ := x.property
  change p.toLinearMap y = (x : H) at hy
  rw [← hy]
  exact congrArg (fun T : H →L[ℂ] H => T y) hp.isIdempotentElem.eq

@[simp] theorem projectionFiberRetraction_inclusion (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    (projectionFiberRetraction p hp).comp (projectionFiberInclusion p hp).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (projectionFiber p hp) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact projectionFiber_fixed p hp x

theorem norm_projectionFiberRetraction_le (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    ‖projectionFiberRetraction p hp‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖p x‖ ≤ 1 * ‖x‖
  exact (p.le_opNorm x).trans (mul_le_mul_of_nonneg_right
    (norm_projection_le_one p hp.isSelfAdjoint.star_eq hp.isIdempotentElem.eq) (norm_nonneg x))

/-- Compression is defined on every operator, even before support is proved. -/
def projectionFiberCompression (p : H →L[ℂ] H) (hp : IsStarProjection p) (T : H →L[ℂ] H) :
    projectionFiber p hp →L[ℂ] projectionFiber p hp :=
  (projectionFiberRetraction p hp).comp (T.comp (projectionFiberInclusion p hp).toContinuousLinearMap)

@[simp] theorem projectionFiberCompression_coe (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (T : H →L[ℂ] H) (x : projectionFiber p hp) :
    (projectionFiberCompression p hp T x : H) = p (T (x : H)) := rfl

/-- A left-supported operator retains its actual action on the range. -/
theorem projectionFiberCompression_apply_of_left_support
    (p : H →L[ℂ] H) (hp : IsStarProjection p) (T : H →L[ℂ] H) (hT : p * T = T)
    (x : projectionFiber p hp) : (projectionFiberCompression p hp T x : H) = T x :=
  congrArg (fun A : H →L[ℂ] H => A (x : H)) hT

/-- Extending the compressed supported operator by zero recovers it. -/
theorem projectionFiberCompression_extension
    (p : H →L[ℂ] H) (hp : IsStarProjection p) (T : H →L[ℂ] H)
    (hleft : p * T = T) (hright : T * p = T) :
    (projectionFiberInclusion p hp).toContinuousLinearMap.comp
      ((projectionFiberCompression p hp T).comp (projectionFiberRetraction p hp)) = T := by
  apply ContinuousLinearMap.ext
  intro x
  change p (T (p x)) = T x
  have hl := congrArg (fun A : H →L[ℂ] H => A (p x)) hleft
  have hr := congrArg (fun A : H →L[ℂ] H => A x) hright
  exact hl.trans hr

/-- No norm is lost by restricting a supported operator to the projection range. -/
theorem norm_projectionFiberCompression
    (p : H →L[ℂ] H) (hp : IsStarProjection p) (T : H →L[ℂ] H)
    (hleft : p * T = T) (hright : T * p = T) :
    ‖projectionFiberCompression p hp T‖ = ‖T‖ := by
  have h := norm_split_extension (projectionFiberInclusion p hp).toContinuousLinearMap
    (projectionFiberRetraction p hp)
    (projectionFiberInclusion p hp).norm_toContinuousLinearMap_le
    (norm_projectionFiberRetraction_le p hp) (projectionFiberRetraction_inclusion p hp)
    (projectionFiberCompression p hp T)
  rw [projectionFiberCompression_extension p hp T hleft hright] at h
  exact h.symm

/-- The same supported restriction preserves every finite operator-matrix
norm; the coordinate inclusions and retractions remain contractive. -/
theorem norm_matrix_projectionFiberCompression
    (p : H →L[ℂ] H) (hp : IsStarProjection p) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hleft : ∀ i j, p * X i j = X i j) (hright : ∀ i j, X i j * p = X i j) :
    ‖matrixOperator (fun i j => projectionFiberCompression p hp (X i j))‖ =
      ‖matrixOperator X‖ := by
  let J := mapCopies (projectionFiberInclusion p hp).toContinuousLinearMap n
  let R := mapCopies (projectionFiberRetraction p hp) n
  have hJ : ‖J‖ ≤ 1 := (norm_mapCopies_le _ _).trans
    (projectionFiberInclusion p hp).norm_toContinuousLinearMap_le
  have hR : ‖R‖ ≤ 1 := (norm_mapCopies_le _ _).trans
    (norm_projectionFiberRetraction_le p hp)
  have hRJ : R.comp J = ContinuousLinearMap.id ℂ (HilbertCopies (projectionFiber p hp) n) := by
    dsimp [R, J]
    rw [← mapCopies_comp_eq, projectionFiberRetraction_inclusion, mapCopies_id_eq]
  have hext : J.comp
      ((matrixOperator (fun i j => projectionFiberCompression p hp (X i j))).comp R) =
        matrixOperator X := by
    apply ContinuousLinearMap.ext
    intro x
    ext i
    change ((projectionFiberInclusion p hp).toContinuousLinearMap
      ((matrixOperator (fun i j => projectionFiberCompression p hp (X i j)))
        (mapCopies (projectionFiberRetraction p hp) n x) i)) = _
    rw [matrixOperator_apply (H := projectionFiber p hp)
      (fun i j => projectionFiberCompression p hp (X i j))
      (mapCopies (projectionFiberRetraction p hp) n x) i, map_sum]
    rw [matrixOperator_apply (H := H) X x i]
    apply Finset.sum_congr rfl
    intro j _
    rw [mapCopies_apply]
    change p (X i j (p (x j))) = X i j (x j)
    have h := congrArg (fun T : H →L[ℂ] H => T (p (x j))) (hleft i j)
    have h' := congrArg (fun T : H →L[ℂ] H => T (x j)) (hright i j)
    exact h.trans h'
  have h := norm_split_extension J R hJ hR hRJ
    (matrixOperator (fun i j => projectionFiberCompression p hp (X i j)))
  rw [hext] at h
  exact h.symm

theorem projectionFiber_invariant (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (T : H →L[ℂ] H) (hcomm : Commute p T) :
    ∀ x ∈ projectionFiber p hp, T x ∈ projectionFiber p hp := by
  rintro x ⟨y, rfl⟩
  refine ⟨T y, ?_⟩
  exact congrArg (fun A : H →L[ℂ] H => A y) hcomm.eq

/-- A commuting operator acts on the closed range by ordinary restriction. -/
def projectionFiberAction (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (T : H →L[ℂ] H) (hcomm : Commute p T) :
    projectionFiber p hp →L[ℂ] projectionFiber p hp :=
  T.restrict (projectionFiber_invariant p hp T hcomm)

@[simp] theorem projectionFiberAction_coe (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (T : H →L[ℂ] H) (hcomm : Commute p T) (x : projectionFiber p hp) :
    (projectionFiberAction p hp T hcomm x : H) = T (x : H) := rfl

theorem projectionFiberAction_eq_compression (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (T : H →L[ℂ] H) (hcomm : Commute p T) :
    projectionFiberAction p hp T hcomm = projectionFiberCompression p hp T := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact (projectionFiber_fixed p hp (projectionFiberAction p hp T hcomm x)).symm

variable {A : Type*} [CStarAlgebra A]

/-- A genuine representation commuting with a projection restricts to a
genuine unital representation on its actual Hilbert range. -/
def projectionFiberRepresentation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (p : H →L[ℂ] H) (hp : IsStarProjection p) (hcomm : ∀ a, Commute p (σ a)) :
    A →⋆ₐ[ℂ] (projectionFiber p hp →L[ℂ] projectionFiber p hp) where
  toFun a := projectionFiberAction p hp (σ a) (hcomm a)
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' a b := by ext x; simp
  map_mul' a b := by ext x; simp [mul_apply_eq_comp]
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : H) (σ (star a) (x : H)) =
      inner ℂ y ((projectionFiberAction p hp (σ a) (hcomm a)).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (y : H) (σ (star a) (x : H)) =
      inner ℂ (σ a (y : H)) (x : H)
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem projectionFiberRepresentation_coe
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (hcomm : ∀ a, Commute p (σ a)) (a : A) (x : projectionFiber p hp) :
    (projectionFiberRepresentation σ p hp hcomm a x : H) = σ a (x : H) := rfl

section Fields

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H]

omit [CompleteSpace H] in
/-- An actual left-support identity gives the corresponding field identity
almost everywhere. -/
theorem ae_field_left_support
    (P T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (p R : Ω → H →L[ℂ] H)
    (hP : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, P f a = p a (f a))
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hPT : P * T = T) : ∀ᵐ a ∂μ, p a * R a = R a := by
  have h := pointwise_field_mul μ P T p R R hP hR (by simpa only [hPT] using hR)
  exact h.mono fun _ ha => ha.symm

omit [CompleteSpace H] in
/-- Right support is also inherited from the actual L² operator equation. -/
theorem ae_field_right_support
    (P T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (p R : Ω → H →L[ℂ] H)
    (hP : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, P f a = p a (f a))
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hTP : T * P = T) : ∀ᵐ a ∂μ, R a * p a = R a := by
  have h := pointwise_field_mul μ T P R p R hR hP (by simpa only [hTP] using hR)
  exact h.mono fun _ ha => ha.symm

/-- Restricting supported fields to their projection fibers loses no
pointwise norm, with support derived from the original operators. -/
theorem ae_norm_projectionFiberCompression
    (P T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (p R : Ω → H →L[ℂ] H)
    (hp : ∀ a, IsStarProjection (p a))
    (hP : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, P f a = p a (f a))
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hPT : P * T = T) (hTP : T * P = T) :
    ∀ᵐ a ∂μ, ‖projectionFiberCompression (p a) (hp a) (R a)‖ = ‖R a‖ := by
  filter_upwards [ae_field_left_support μ P T p R hP hR hPT,
    ae_field_right_support μ P T p R hP hR hTP] with a hl hr
  exact norm_projectionFiberCompression (p a) (hp a) (R a) hl hr

/-- The restricted field has the same action on every section taking
values in the projection fibers. -/
theorem projectionFiberCompression_section_action
    (P T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (p R : Ω → H →L[ℂ] H)
    (hp : ∀ a, IsStarProjection (p a))
    (hP : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, P f a = p a (f a))
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hPT : P * T = T) (f : Lp H 2 μ)
    (v : ∀ a, projectionFiber (p a) (hp a))
    (hv : ∀ᵐ a ∂μ, (v a : H) = f a) :
    ∀ᵐ a ∂μ, (projectionFiberCompression (p a) (hp a) (R a) (v a) : H) = T f a := by
  filter_upwards [ae_field_left_support μ P T p R hP hR hPT, hR f, hv]
    with a hl hr hv
  rw [projectionFiberCompression_apply_of_left_support _ _ _ hl, hv]
  exact hr.symm

end Fields

end KadisonSimilarity

end

end OAI
