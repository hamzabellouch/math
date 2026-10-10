import OAI.Analysis.BoundedHochschild.CentralPrimitives
import OAI.Analysis.BoundedHochschild.OperatorPrimitives

namespace OAI

/-!
# The classical input for algebras represented as full operator algebras

Kadison--Ringrose, *Cohomology of operator algebras I* (1971), Theorem 4.4,
includes the type I vanishing result. Here its full-operator-algebra case is
proved using the explicit rank-one homotopy in `OperatorPrimitives`, and is
transported across an actual star algebra equivalence. No cohomological
vanishing hypothesis is assumed.
-/

noncomputable section

namespace BoundedHochschild

section Transport
variable {M N : Type*} [CStarAlgebra M] [CStarAlgebra N]

/-- An algebra equivalence gives mutually inverse contractive expectation maps. -/
def expectedEmbeddingOfStarAlgEquiv (φ : N ≃⋆ₐ[ℂ] M) : ExpectedEmbedding N M where
  includeMap := φ.toAlgEquiv.toLinearMap.mkContinuous 1 (fun a => by
    change ‖φ a‖ ≤ 1 * ‖a‖
    rw [one_mul, StarAlgEquiv.norm_map])
  expectMap := φ.symm.toAlgEquiv.toLinearMap.mkContinuous 1 (fun a => by
    change ‖φ.symm a‖ ≤ 1 * ‖a‖
    rw [one_mul, StarAlgEquiv.norm_map])
  include_mul := fun a b => map_mul φ a b
  include_one := map_one φ
  include_star := fun a => map_star φ a
  include_norm := StarAlgEquiv.norm_map φ
  expect_norm := fun a => (StarAlgEquiv.norm_map φ.symm a).le
  retract := φ.symm_apply_apply
  left_module := fun a x => by
    change φ.symm (φ a * x) = a * φ.symm x
    rw [map_mul, φ.symm_apply_apply]
  right_module := fun x a => by
    change φ.symm (x * φ a) = φ.symm x * a
    rw [map_mul, φ.symm_apply_apply]

lemma expectedEmbeddingOfStarAlgEquiv_surjective (φ : N ≃⋆ₐ[ℂ] M) :
    Function.Surjective (expectedEmbeddingOfStarAlgEquiv φ).includeMap :=
  φ.surjective

namespace ExpectedEmbedding

/-- For a surjective inclusion the finite exactness identity holds at every tuple. -/
lemma extend_primitive_of_surjective (E : ExpectedEmbedding N M)
    (hE : Function.Surjective E.includeMap) {n : ℕ}
    (f : Cochain M (n + 1)) (g : Cochain N n)
    (hg : ∀ x, differentialValue g x = E.restrict f x) :
    ∀ x, differentialValue (E.extend g) x = f x := by
  intro x
  exact E.finite_exactness f g hg Set.univ (fun a _ => hE a)
    (fun x _ => hE (f x)) x (fun _ => Set.mem_univ _)

end ExpectedEmbedding

/-- A norm-controlled primitive is preserved by a star algebra equivalence. -/
theorem primitive_of_starAlgEquiv (φ : N ≃⋆ₐ[ℂ] M) {n : ℕ}
    (f : Cochain M (n + 1))
    (hN : ∀ F : Cochain N (n + 1), (∀ x, differentialValue F x = 0) →
      ∃ g : Cochain N n, ‖g‖ ≤ ‖F‖ ∧ ∀ x, differentialValue g x = F x)
    (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  let E := expectedEmbeddingOfStarAlgEquiv φ
  obtain ⟨g, hgn, hg⟩ := hN (E.restrict f) (E.restrict_cocycle f hf)
  exact ⟨E.extend g, (E.extend_norm g).trans (hgn.trans (E.restrict_norm f)),
    E.extend_primitive_of_surjective (expectedEmbeddingOfStarAlgEquiv_surjective φ) f g hg⟩

end Transport

/-- The non-II₁ classical input is discharged for any actual presentation as `B(H)`.
The rank-one homotopy also provides the norm-one primitive bound. -/
theorem primitive_of_full_operator_equiv
    {M H : Type*} [CStarAlgebra M]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] M) {n : ℕ}
    (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x :=
  primitive_of_starAlgEquiv φ f (fun F hF => primitive_on_operators F hF) hf

end BoundedHochschild

end

end OAI
