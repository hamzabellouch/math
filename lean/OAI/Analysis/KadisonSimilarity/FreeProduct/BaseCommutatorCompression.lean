import OAI.Analysis.KadisonSimilarity.Tracial.TracialBaseSpace
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI

/-! Compression of commutators with base-algebra elements needs no invariance
hypothesis on the other operator. This also restores the original operator
after the free-product symmetrization. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- Faithfulness of the tracial algebra vectors makes left multiplication
faithful as an algebra representation. -/
theorem left_injective (hfaithful : Function.Injective G.vector) :
    Function.Injective G.left := by
  intro a b hab
  apply hfaithful
  have hv := congrArg (fun T : H →L[ℂ] H => T (G.vector 1)) hab
  simpa only [G.left_vector, mul_one] using hv

/-- The faithful tracial representation preserves the C-star norm. -/
theorem norm_left (hfaithful : Function.Injective G.vector) (a : P) :
    ‖G.left a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map G.left (G.left_injective hfaithful) a

/-- The adjoint base inclusion intertwines every base-algebra element. -/
theorem baseInclusion_adjoint_intertwines (a : A) :
    (G.baseInclusion A).toContinuousLinearMap.adjoint.comp (G.left (a : P)) =
      (G.baseRepresentation A a).comp (G.baseInclusion A).toContinuousLinearMap.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (G.baseInclusion_intertwines A (star a))
  have hleft : (G.left ((star a : A) : P)).adjoint = G.left (a : P) := by
    change (G.left (star (a : P))).adjoint = G.left (a : P)
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
  have hbase : (G.baseRepresentation A (star a)).adjoint = G.baseRepresentation A a := by
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
  simpa only [ContinuousLinearMap.adjoint_comp, hleft, hbase] using h


/-- Compression commutes with the commutator against a base element. -/
theorem baseOperator_commutator_subalgebra (Y : H →L[ℂ] H) (a : A) :
    G.baseOperator A (commutator Y (G.left (a : P))) =
      commutator (G.baseOperator A Y) (G.baseRepresentation A a) := by
  unfold baseOperator commutator
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  rw [G.baseInclusion_intertwines A a]
  simp only [← ContinuousLinearMap.comp_assoc]
  rw [G.baseInclusion_adjoint_intertwines A a]

/-- Equal base compressions preserve exactly the compressed commutator used
by the free-product corner theorem, even before invariance is established. -/
theorem baseOperator_commutator_eq_of_compression_eq (Y Z : H →L[ℂ] H)
    (h : G.baseOperator A Y = G.baseOperator A Z) (a : A) :
    G.baseOperator A (commutator Y (G.left (a : P))) =
      G.baseOperator A (commutator Z (G.left (a : P))) := by
  rw [G.baseOperator_commutator_subalgebra A Y a,
    G.baseOperator_commutator_subalgebra A Z a, h]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
