import OAI.AlgebraicGeometry.StableCoordinate.WeightedInitialIdeal
import OAI.AlgebraicGeometry.StableCoordinate.GradedRelation

namespace OAI

/-!
# The exact initial relation of the source hypersurface

For the five independent variables `p,s,u,F,J`, with integer weights
`(-1,0,0,1,1)`, this file proves that the initial ideal of `(H)` is exactly
`(Hstar)`. It also gives the actual homogeneous kernel criterion in terms of
the quotient rings `A` and `G`, without assuming an associated-graded isomorphism.
-/

namespace StableCoordinate.PrincipalInitialRelation

noncomputable section

open MvPolynomial WeightedInitial Obstruction

variable (k : Type*) [CommRing k]

/-- The original relation has no monomials above weight one. -/
theorem H_bounded : Bounded presentationWeight (H k) 1 := by
  unfold H
  apply (bounded_of_homogeneous (Hstar_homogeneous k)).sub
  have hu : (X 2 : P k 5).IsWeightedHomogeneous presentationWeight 0 := by
    simpa [presentationWeight] using isWeightedHomogeneous_X k presentationWeight (2 : Fin 5)
  exact (bounded_of_homogeneous hu).mono (by omega)

/-- The original relation has actual highest integer weight one. -/
theorem H_isTopDegree [Nontrivial k] : IsTopDegree presentationWeight (H k) 1 := by
  refine ⟨H_bounded k, ?_⟩
  rw [H_degree_one_component k]
  intro hzero
  exact p_not_dvd_Hstar k (hzero ▸ dvd_zero _)

/-- The leading weight of a product by the exact relation is obtained by
multiplying the leading component by the exact polynomial `Hstar`. -/
theorem component_mul_H (q : P k 5) (d : ℤ)
    (hq : Bounded presentationWeight q d) :
    weightedHomogeneousComponent presentationWeight (d + 1) (q * H k) =
      weightedHomogeneousComponent presentationWeight d q * Hstar k := by
  rw [component_mul_of_bounded hq (H_bounded k), H_degree_one_component k]

variable [IsDomain k]

/-- The principal initial-ideal identity for the exact source relation. -/
theorem initialIdeal_idealA :
    initialIdeal presentationWeight (idealA k) = idealG k := by
  unfold idealA idealG
  rw [initialIdeal_span_singleton (H_isTopDegree k), H_degree_one_component k]

/-- A homogeneous polynomial has a lower-weight representative modulo `H`
if and only if it belongs to `(Hstar)`. -/
theorem homogeneous_lower_iff (p : P k 5) (d : ℤ)
    (hp : p.IsWeightedHomogeneous presentationWeight d) :
    (∃ r : P k 5, Bounded presentationWeight r (d - 1) ∧ p - r ∈ idealA k) ↔
      p ∈ idealG k := by
  simpa only [idealA, idealG, H_degree_one_component k] using
    homogeneous_quotient_kernel_iff presentationWeight (H k) 1
      (H_isTopDegree k).1 (H_isTopDegree k).2 hp

/-- The same exact kernel criterion, stated directly in the two quotient rings.
This is the degreewise algebraic interface used to identify `G` with `gr A`. -/
theorem quotient_homogeneous_lower_iff (p : P k 5) (d : ℤ)
    (hp : p.IsWeightedHomogeneous presentationWeight d) :
    (∃ r : P k 5, Bounded presentationWeight r (d - 1) ∧
      Ideal.Quotient.mk (idealA k) p = Ideal.Quotient.mk (idealA k) r) ↔
      Ideal.Quotient.mk (idealG k) p = 0 := by
  simpa only [Ideal.Quotient.eq, Ideal.Quotient.eq_zero_iff_mem] using
    homogeneous_lower_iff k p d hp

end
end StableCoordinate.PrincipalInitialRelation

end OAI
