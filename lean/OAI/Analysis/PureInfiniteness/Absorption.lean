import OAI.Analysis.WeakInfiniteness.NuclearExact
import OAI.Analysis.WeakInfiniteness.OInfinityCriterion

namespace OAI

/-!
# Cuntz-algebra absorption

Absorption is expressed by a star-algebra isomorphism with the minimal tensor
product. The implication from nuclear strong pure infiniteness is the
specialization to O∞ of E. Kirchberg, *Central sequences in C*-algebras and
strongly purely infinite algebras*, in *Operator Algebras: The Abel Symposium
2004* (2006), pp. 175--231, Proposition 4.4(4),(5) and Remark 4.6, together
with the central-sequence embedding preceding Proposition 4.4.

For a possibly nonunital separable algebra, the unital central embedding is into
`(Aω ∩ A') / Ann(A, Aω)`. The zero algebra is included.

Source: <https://abelsymposium.no/symp2004/preprints/kirchberg.pdf>.
-/

namespace WeakPureInfiniteness

universe u

/-- Absorption of the Cuntz algebra, expressed by a star-algebra isomorphism. -/
def AbsorbsOInfinity (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  Nonempty (A ≃⋆ₐ[ℂ] MinimalTensor A OInfinity)

variable (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A]
  [StarOrderedRing A]

/-- Nuclear strong pure infiniteness implies absorption for a separable algebra,
including the zero algebra, without a unit or simplicity hypothesis. -/
def KirchbergOInfinityAbsorption [TopologicalSpace.SeparableSpace A] : Prop :=
  Nuclear A → StronglyPurelyInfinite A → AbsorbsOInfinity A

omit [PartialOrder A] [StarOrderedRing A] in
/-- A zero algebra has a zero minimal tensor product with `OInfinity`. -/
theorem oInfinityTensor_subsingleton [Subsingleton A] :
    Subsingleton (MinimalTensor A OInfinity) := by
  have hle : minimalTensorSubalgebra A OInfinity ≤ ⊥ := by
    unfold minimalTensorSubalgebra
    apply NonUnitalStarSubalgebra.topologicalClosure_minimal
    · apply NonUnitalStarAlgebra.adjoin_le
      rintro _ ⟨⟨a, b⟩, rfl⟩
      change spatialElementary a b ∈
        (⊥ : NonUnitalStarSubalgebra ℂ (SpatialAmbient A OInfinity))
      rw [Subsingleton.elim a 0, spatialElementary_zero_left]
      exact zero_mem _
    · rw [NonUnitalStarAlgebra.coe_bot]
      exact isClosed_singleton
  refine ⟨fun x y => ?_⟩
  apply Subtype.ext
  exact ((NonUnitalStarAlgebra.mem_bot).mp (hle x.property)).trans
    ((NonUnitalStarAlgebra.mem_bot).mp (hle y.property)).symm

private def starEquivOfSubsingleton (R X Y : Type*) [Add X] [Add Y] [Mul X] [Mul Y]
    [SMul R X] [SMul R Y] [Star X] [Star Y] [Zero X] [Zero Y]
    [Subsingleton X] [Subsingleton Y] : X ≃⋆ₐ[R] Y where
  toFun := fun _ => 0
  invFun := fun _ => 0
  left_inv := fun _ => Subsingleton.elim _ _
  right_inv := fun _ => Subsingleton.elim _ _
  map_add' := fun _ _ => Subsingleton.elim _ _
  map_mul' := fun _ _ => Subsingleton.elim _ _
  map_star' := fun _ => Subsingleton.elim _ _
  map_smul' := fun _ _ => Subsingleton.elim _ _

omit [PartialOrder A] [StarOrderedRing A] in
/-- The zero-algebra absorption isomorphism needs no nuclearity premise. -/
theorem absorbsOInfinity_of_subsingleton [Subsingleton A] : AbsorbsOInfinity A := by
  have := oInfinityTensor_subsingleton A
  unfold AbsorbsOInfinity
  exact ⟨starEquivOfSubsingleton ℂ A _⟩

/-- The published absorption input is discharged for the zero algebra. -/
theorem kirchbergOInfinityAbsorption_of_subsingleton
    [TopologicalSpace.SeparableSpace A] [Subsingleton A] :
    KirchbergOInfinityAbsorption A := by
  intro _ _
  exact absorbsOInfinity_of_subsingleton A

end WeakPureInfiniteness

end OAI
