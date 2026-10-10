import OAI.Analysis.BoundedHochschild.Conditional
import OAI.Analysis.BoundedHochschild.OperatorTransport

namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners
open scoped ComplexOrder

universe u

section CornerEquivalence
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- The unit corner is canonically the original algebra. -/
def unitCornerEquiv : Corner (1 : M) (IsStarProjection.one M) ≃⋆ₐ[ℂ] M where
  toFun := Subtype.val
  invFun := fun a => ⟨a, by simp only [mem_corner, one_mul, mul_one, and_self]⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_mul' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  map_star' := fun _ => rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma unitCornerEquiv_apply (a : Corner (1 : M) (IsStarProjection.one M)) :
    unitCornerEquiv a = (a : M) := rfl

/-- Absence of abelian corners is invariant under a star algebra equivalence. -/
lemma noAbelianCorners_of_equiv
    {N : Type u} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
    (φ : N ≃⋆ₐ[ℂ] M) (hM : PopaTypeII.NoAbelianCorners M) :
    PopaTypeII.NoAbelianCorners N := by
  intro p hp hp0
  have hφp : IsStarProjection (φ p) := by
    constructor
    · change φ p * φ p = φ p
      rw [← map_mul, hp.isIdempotentElem.eq]
    · change star (φ p) = φ p
      rw [← map_star, hp.isSelfAdjoint.star_eq]
  obtain ⟨a, b, hab⟩ := hM (φ p) hφp (fun h => hp0 (φ.injective (by simpa using h)))
  let pull (a : PopaCorner.algebra hφp) : PopaCorner.algebra hp :=
    ⟨φ.symm (a : M), by
      constructor
      · apply φ.injective
        change φ (p * φ.symm (a : M)) = φ (φ.symm (a : M))
        rw [map_mul, φ.apply_symm_apply]
        exact a.property.1
      · apply φ.injective
        change φ (φ.symm (a : M) * p) = φ (φ.symm (a : M))
        rw [map_mul, φ.apply_symm_apply]
        exact a.property.2⟩
  refine ⟨pull a, pull b, ?_⟩
  intro h
  apply hab
  apply Subtype.ext
  have hh := congrArg (fun x : PopaCorner.algebra hp => φ (x : N)) h.eq
  change φ (φ.symm (a : M) * φ.symm (b : M)) =
    φ (φ.symm (b : M) * φ.symm (a : M)) at hh
  change (a : M) * (b : M) = (b : M) * (a : M)
  simpa only [map_mul, φ.apply_symm_apply] using hh

end CornerEquivalence

section TracialCorner
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

/-- The original trace restricted along the canonical unit-corner equivalence. -/
def unitCornerTrace : Corner (1 : M) (IsStarProjection.one M) →ₚ[ℂ] ℂ where
  toLinearMap := τ.toLinearMap.comp (unitCornerEquiv.toAlgEquiv.toLinearMap)
  monotone' := fun _ _ h => τ.monotone h

omit [StarOrderedRing M] in
@[simp] lemma unitCornerTrace_apply (a : Corner (1 : M) (IsStarProjection.one M)) :
    unitCornerTrace τ a = τ (a : M) := rfl

lemma unitCornerTrace_normal (hτ : TraceInPredual e τ) :
    TraceInPredual (cornerPredualEquiv (1 : M) (IsStarProjection.one M) e)
      (unitCornerTrace τ) := by
  obtain ⟨z, hz⟩ := hτ
  refine ⟨Submodule.Quotient.mk z, fun a => ?_⟩
  rw [cornerPredualEquiv_symm_mk]
  exact hz (a : M)

/-- All data required by the tracial primitive theorem survives passing to the unit corner. -/
theorem tracialTypeII_unitCorner
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (hfaith : ∀ a : M, τ (star a * a) = 0 → a = 0) (h1 : τ 1 = 1)
    (hII : PopaTypeII.NoTypeICentralPart M) :
    TracialTypeII (Corner (1 : M) (IsStarProjection.one M)) := by
  let eC := cornerPredualEquiv (1 : M) (IsStarProjection.one M) e
  let τC := unitCornerTrace τ
  have hτC : TraceInPredual eC τC := unitCornerTrace_normal e τ hτ
  have htrC (a b : Corner (1 : M) (IsStarProjection.one M)) : τC (a * b) = τC (b * a) :=
    htr (a : M) (b : M)
  have hfaithC (a : Corner (1 : M) (IsStarProjection.one M))
      (ha : τC (star a * a) = 0) : a = 0 := Subtype.ext (hfaith (a : M) ha)
  have h1C : τC 1 = 1 := h1
  have hdiff := noAbelianCorners_of_equiv unitCornerEquiv
    ((PopaTypeII.noTypeICentralPart_iff e τ hτ htr hfaith h1).mp hII)
  have hIIC := (PopaTypeII.noTypeICentralPart_iff eC τC hτC htrC hfaithC h1C).mpr hdiff
  exact ⟨CornerPredual (1 : M) (IsStarProjection.one M) e,
    inferInstance, inferInstance, inferInstance, eC, τC, hτC, htrC, hfaithC, h1C, hIIC⟩

end TracialCorner

section Decomposition
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
/-- Every element of the zero corner is zero. -/
lemma zeroCorner_subsingleton : Subsingleton (Corner (0 : M) (IsStarProjection.zero M)) := by
  refine ⟨fun a b => Subtype.ext ?_⟩
  have ha : (a : M) = 0 := by simpa only [zero_mul] using a.property.1.symm
  have hb : (b : M) = 0 := by simpa only [zero_mul] using b.property.1.symm
  exact ha.trans hb.symm

/-- The zero corner cannot contain a nonzero type II₁ central summand. -/
lemma zeroCorner_noTypeII1Summand :
    NoTypeII1Summand (Corner (0 : M) (IsStarProjection.zero M)) := by
  let := zeroCorner_subsingleton (M := M)
  intro z _ _ _ _
  exact Subsingleton.elim z 0

theorem centralDecompositionInput_of_tracialTypeII (hM : TracialTypeII M) :
    CentralDecompositionInput M := by
  rcases hM with ⟨X, hX, hXS, hXC, e, τ, hτ, htr, hfaith, h1, hII⟩
  let := hX
  let := hXS
  let := hXC
  let p : Option PUnit → M := fun i => match i with
    | none => 0
    | some _ => 1
  let hp : ∀ i, IsStarProjection (p i) := fun i => by
    cases i with
    | none => exact IsStarProjection.zero M
    | some _ => exact IsStarProjection.one M
  refine ⟨{
    Index := PUnit
    projection := p
    isProjection := hp
    central := ?_
    orthogonal := ?_
    total := ?_
    exceptional := ?_
    tracial := ?_ }⟩
  · intro i a
    cases i <;> simp [p]
  · intro i j hij
    cases i <;> cases j <;> simp_all [p]
  · intro x hx
    simpa only [p, one_mul] using hx (some PUnit.unit)
  · exact zeroCorner_noTypeII1Summand
  · intro i
    exact tracialTypeII_unitCorner e τ hτ htr hfaith h1 hII

end Decomposition

end KadisonRingrose
end BoundedHochschild

end

end OAI
