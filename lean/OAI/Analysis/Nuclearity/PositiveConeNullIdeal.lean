import OAI.Analysis.Nuclearity.PositiveConeIdeal
import OAI.Analysis.JiangSu.Nonunital.ClosedIdealBasic

namespace OAI

/-! The closed two-sided ideal occurring in KR02 Lemma 7.17(ii).
It is constructed from square nullspaces of positive functionals; stability
under coefficient conjugation supplies right multiplication and the star law. -/

noncomputable section
open scoped Topology ComplexOrder
open selfAdjoint

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def conjugatePositiveFunctional (φ : A →ₚ[ℂ] ℂ) (d : A) : A →ₚ[ℂ] ℂ where
  toLinearMap :=
    { toFun := fun a => φ (star d * a * d)
      map_add' := by intro a b; simp only [mul_add, add_mul, map_add]
      map_smul' := by intro c a; simp only [mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply] }
  monotone' := fun _ _ h => φ.monotone (star_left_conjugate_le_conjugate h d)

@[simp] lemma conjugatePositiveFunctional_apply (φ : A →ₚ[ℂ] ℂ) (d a : A) :
    conjugatePositiveFunctional φ d a = φ (star d * a * d) := rfl

def commonSquareNull (K : Set (A →ₚ[ℂ] ℂ)) (x : A) : Prop :=
  ∀ φ ∈ K, φ (star x * x) = 0

lemma positiveFunctional_mixed_eq_zero (φ : A →ₚ[ℂ] ℂ) (x y : A)
    (hx : φ (star x * x) = 0) : φ (star x * y) = 0 := by
  have h := PositiveLinearMap.norm_map_star_mul_le φ x y
  rw [hx, norm_zero, Real.sqrt_zero, zero_mul] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

lemma commonSquareNull_add (K : Set (A →ₚ[ℂ] ℂ)) {x y : A}
    (hx : commonSquareNull K x) (hy : commonSquareNull K y) :
    commonSquareNull K (x + y) := by
  intro φ hφ
  have hxy := positiveFunctional_mixed_eq_zero φ x y (hx φ hφ)
  have hyx := positiveFunctional_mixed_eq_zero φ y x (hy φ hφ)
  simp only [star_add, add_mul, mul_add, map_add, hx φ hφ, hy φ hφ, hxy, hyx,
    add_zero]

omit [StarOrderedRing A] in
lemma commonSquareNull_smul (K : Set (A →ₚ[ℂ] ℂ)) {x : A}
    (hx : commonSquareNull K x) (c : ℂ) : commonSquareNull K (c • x) := by
  intro φ hφ
  simp only [star_smul, smul_mul_assoc, mul_smul_comm, map_smul, hx φ hφ, smul_zero]

lemma commonSquareNull_mul_right (K : Set (A →ₚ[ℂ] ℂ))
    (hconj : ∀ φ ∈ K, ∀ d : A, conjugatePositiveFunctional φ d ∈ K)
    {x : A} (hx : commonSquareNull K x) (d : A) : commonSquareNull K (x * d) := by
  intro φ hφ
  have h := hx (conjugatePositiveFunctional φ d) (hconj φ hφ d)
  simpa only [conjugatePositiveFunctional_apply, star_mul, mul_assoc] using h

lemma commonSquareNull_star (K : Set (A →ₚ[ℂ] ℂ))
    (hconj : ∀ φ ∈ K, ∀ d : A, conjugatePositiveFunctional φ d ∈ K)
    {x : A} (hx : commonSquareNull K x) : commonSquareNull K (star x) := by
  intro φ hφ
  have h := hx (conjugatePositiveFunctional φ (star x)) (hconj φ hφ (star x))
  have hsquare : φ (star (x * star x) * (x * star x)) = 0 := by
    simpa only [conjugatePositiveFunctional_apply, star_mul, star_star, mul_assoc] using h
  simpa only [star_star] using positiveFunctional_eq_zero_of_square φ (x * star x) hsquare

lemma commonSquareNull_mul_left (K : Set (A →ₚ[ℂ] ℂ))
    (hconj : ∀ φ ∈ K, ∀ d : A, conjugatePositiveFunctional φ d ∈ K)
    {x : A} (hx : commonSquareNull K x) (d : A) : commonSquareNull K (d * x) := by
  have hs := commonSquareNull_star K hconj hx
  have hr := commonSquareNull_mul_right K hconj hs (star d)
  simpa only [star_mul, star_star] using commonSquareNull_star K hconj hr

lemma isClosed_commonSquareNull (K : Set (A →ₚ[ℂ] ℂ)) :
    IsClosed {x : A | commonSquareNull K x} := by
  have he : {x : A | commonSquareNull K x} =
      ⋂ (φ : A →ₚ[ℂ] ℂ) (_hφ : φ ∈ K), {x : A | φ (star x * x) = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, commonSquareNull]
  rw [he]
  exact isClosed_iInter fun φ => isClosed_iInter fun _ =>
    isClosed_eq ((map_continuous φ).comp (continuous_star.mul continuous_id)) continuous_const

/-- The common square nullspace is a genuine closed star ideal, including for
nonunital algebras. No ideal-generation hypothesis is built into the definition. -/
def commonSquareNullIdeal (K : Set (A →ₚ[ℂ] ℂ))
    (hconj : ∀ φ ∈ K, ∀ d : A, conjugatePositiveFunctional φ d ∈ K) :
    NonunitalClosedIdeal.Ideal A where
  module :=
    { carrier := {x | commonSquareNull K x}
      zero_mem' := by intro φ _; simp
      add_mem' := commonSquareNull_add K
      smul_mem' := fun c _ hx => commonSquareNull_smul K hx c }
  mul_left := fun d _ hx => commonSquareNull_mul_left K hconj hx d
  mul_right := fun _ d hx => commonSquareNull_mul_right K hconj hx d
  star_mem := fun _ hx => commonSquareNull_star K hconj hx
  closed := isClosed_commonSquareNull K

lemma commonSquareNullIdeal_mem_iff (K : Set (A →ₚ[ℂ] ℂ))
    (hconj : ∀ φ ∈ K, ∀ d : A, conjugatePositiveFunctional φ d ∈ K) (x : A) :
    x ∈ (commonSquareNullIdeal K hconj).module ↔ ∀ φ ∈ K, φ (star x * x) = 0 := Iff.rfl

lemma positiveFunctional_vanishes_commonSquareNull
    (K : Set (A →ₚ[ℂ] ℂ)) {φ : A →ₚ[ℂ] ℂ} (hφ : φ ∈ K)
    {x : A} (hx : commonSquareNull K x) : φ x = 0 :=
  positiveFunctional_eq_zero_of_square φ x (hx φ hφ)

omit [StarOrderedRing A] in
lemma positiveLinearMap_ext_selfAdjoint (φ ψ : A →ₚ[ℂ] ℂ)
    (h : ∀ a : selfAdjoint A, φ (a : A) = ψ (a : A)) : φ = ψ := by
  ext a
  rw [← realPart_add_I_smul_imaginaryPart a]
  simp only [map_add, map_smul, h]

def complexifyWeakPositive (φ : WeakDual ℝ (selfAdjoint A))
    (hφ : ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ φ a) : A →ₚ[ℂ] ℂ :=
  positiveRealComplexification (WeakDual.toStrongDual φ).toLinearMap hφ

@[simp] lemma complexifyWeakPositive_apply (φ : WeakDual ℝ (selfAdjoint A))
    (hφ : ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ φ a) (a : selfAdjoint A) :
    complexifyWeakPositive φ hφ (a : A) = (φ a : ℂ) :=
  positiveRealComplexification_apply _ _ _

def positiveConeComplexification (K : Set (WeakDual ℝ (selfAdjoint A)))
    (hpositive : ∀ φ ∈ K, ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ φ a) :
    Set (A →ₚ[ℂ] ℂ) :=
  {ψ | ∃ φ, ∃ hφ : φ ∈ K, ψ = complexifyWeakPositive φ (hpositive φ hφ)}

lemma positiveConeComplexification_conjugate
    (K : Set (WeakDual ℝ (selfAdjoint A)))
    (hpositive : ∀ φ ∈ K, ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ φ a)
    (hconj : ∀ φ ∈ K, ∀ d : A, conjugateRealFunctional φ d ∈ K) :
    ∀ ψ ∈ positiveConeComplexification K hpositive, ∀ d : A,
      conjugatePositiveFunctional ψ d ∈ positiveConeComplexification K hpositive := by
  rintro ψ ⟨φ, hφ, rfl⟩ d
  refine ⟨conjugateRealFunctional φ d, hconj φ hφ d, ?_⟩
  apply positiveLinearMap_ext_selfAdjoint
  intro a
  change complexifyWeakPositive φ (hpositive φ hφ)
      ((selfAdjointConjugation d a : selfAdjoint A) : A) = _
  rw [complexifyWeakPositive_apply, complexifyWeakPositive_apply]
  rfl

/-- The closed ideal attached to the real weak-star cone in Lemma 7.17(ii). -/
def realPositiveConeNullIdeal
    (K : Set (WeakDual ℝ (selfAdjoint A)))
    (hpositive : ∀ φ ∈ K, ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ φ a)
    (hconj : ∀ φ ∈ K, ∀ d : A, conjugateRealFunctional φ d ∈ K) :
    NonunitalClosedIdeal.Ideal A :=
  commonSquareNullIdeal (positiveConeComplexification K hpositive)
    (positiveConeComplexification_conjugate K hpositive hconj)

lemma mem_realPositiveConeNullIdeal_iff
    (K : Set (WeakDual ℝ (selfAdjoint A)))
    (hpositive : ∀ φ ∈ K, ∀ a : selfAdjoint A, 0 ≤ (a : A) → 0 ≤ φ a)
    (hconj : ∀ φ ∈ K, ∀ d : A, conjugateRealFunctional φ d ∈ K) (x : A) :
    x ∈ (realPositiveConeNullIdeal K hpositive hconj).module ↔
      ∀ φ ∈ K, φ ⟨star x * x, IsSelfAdjoint.star_mul_self x⟩ = 0 := by
  constructor
  · intro hx φ hφ
    have hh := hx (complexifyWeakPositive φ (hpositive φ hφ)) ⟨φ, hφ, rfl⟩
    change complexifyWeakPositive φ (hpositive φ hφ)
      ((⟨star x * x, IsSelfAdjoint.star_mul_self x⟩ : selfAdjoint A) : A) = 0 at hh
    rw [complexifyWeakPositive_apply] at hh
    exact Complex.ofReal_eq_zero.mp hh
  · rintro hx ψ ⟨φ, hφ, rfl⟩
    change complexifyWeakPositive φ (hpositive φ hφ)
      ((⟨star x * x, IsSelfAdjoint.star_mul_self x⟩ : selfAdjoint A) : A) = 0
    rw [complexifyWeakPositive_apply, hx φ hφ, Complex.ofReal_zero]

end WeakPureInfiniteness

end

end OAI
