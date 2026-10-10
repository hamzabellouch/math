import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialOrbitExterior

namespace OAI

/-! # Polynomial relations detected on an invariant linear subspace -/

noncomputable section
namespace PolycyclicRecognition
variable {K V W A : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [CommRing A] [Algebra K A]

theorem polynomialOperator_detector {k : ℕ}
    (α : MvPolynomial (Fin k) K →ₐ[K] Module.End K V)
    (β : MvPolynomial (Fin k) K →ₐ[K] A) (L : V →ₗ[K] A)
    (h : ∀ i v, L (α (MvPolynomial.X i) v) = β (MvPolynomial.X i) * L v)
    (p : MvPolynomial (Fin k) K) (v : V) :
    L (α p v) = β p * L v := by
  induction p using MvPolynomial.induction_on generalizing v with
  | C c =>
    change L (α (algebraMap K (MvPolynomial (Fin k) K) c) v) =
      β (algebraMap K (MvPolynomial (Fin k) K) c) * L v
    rw [α.commutes, β.commutes]
    change L (c • v) = algebraMap K A c * L v
    rw [map_smul, Algebra.smul_def]
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq, add_mul]
  | mul_X p i hp =>
    rw [map_mul, Module.End.mul_apply, hp, h, map_mul, mul_assoc]

theorem polynomialOperator_intertwines {k : ℕ}
    (α : MvPolynomial (Fin k) K →ₐ[K] Module.End K W)
    (γ : MvPolynomial (Fin k) K →ₐ[K] Module.End K V) (E : V →ₗ[K] W)
    (h : ∀ i v, E (γ (MvPolynomial.X i) v) = α (MvPolynomial.X i) (E v))
    (p : MvPolynomial (Fin k) K) (v : V) : E (γ p v) = α p (E v) := by
  induction p using MvPolynomial.induction_on generalizing v with
  | C c =>
    change E (γ (algebraMap K (MvPolynomial (Fin k) K) c) v) =
      α (algebraMap K (MvPolynomial (Fin k) K) c) (E v)
    rw [γ.commutes, α.commutes]
    exact E.map_smul c v
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | mul_X p i hp => rw [map_mul, Module.End.mul_apply, hp, h, map_mul, Module.End.mul_apply]

theorem polynomialOperator_relation_detected [IsDomain A] {k : ℕ}
    (α : MvPolynomial (Fin k) K →ₐ[K] Module.End K W)
    (γ : MvPolynomial (Fin k) K →ₐ[K] Module.End K V)
    (β : MvPolynomial (Fin k) K →ₐ[K] A) (E : V →ₗ[K] W)
    (hE : Function.Injective E) (L : V →ₗ[K] A)
    (hγ : ∀ i v, E (γ (MvPolynomial.X i) v) = α (MvPolynomial.X i) (E v))
    (hβ : ∀ i v, L (γ (MvPolynomial.X i) v) = β (MvPolynomial.X i) * L v)
    (v : V) (hv : L v ≠ 0) {p : MvPolynomial (Fin k) K} (hp : α p = 0) : β p = 0 := by
  have hz : γ p v = 0 := by
    apply hE
    rw [polynomialOperator_intertwines α γ E hγ, hp, LinearMap.zero_apply, map_zero]
  have he := polynomialOperator_detector γ β L hβ p v
  rw [hz, map_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_right hv

end PolycyclicRecognition

end

end OAI
