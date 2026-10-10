import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeNormalRigidity

namespace OAI

noncomputable section
namespace PiExponent
open Module MvPolynomial NormalBasisRigidity

variable {C E ι : Type*} [Field C] [CharZero C] [Field E] [Algebra C E] [Fintype ι]

theorem polynomialNormal_mkQ_ne_zero_of_kernel
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥) :
    (polynomialTangent φ Q).mkQ ≠ 0 := by
  classical
  intro hzero
  have htop : polynomialTangent φ Q = ⊤ := by
    rw [← Submodule.ker_mkQ (polynomialTangent φ Q), hzero, LinearMap.ker_zero]
  apply hQ
  apply ideal_eq_bot_of_pderiv_stable Q
  · intro h
    have hh := (hker 1).mpr (by rw [h]; trivial)
    exact (one_ne_zero : (1 : E) ≠ 0) (by simpa only [map_one] using hh)
  · intro p hp i
    apply (hker _).mp
    have ht : (Pi.single i 1 : ι → E) ∈ polynomialTangent φ Q := by rw [htop]; trivial
    change polynomialJacobian φ Q (Pi.single i 1) = 0 at ht
    have hh := congrFun ht ⟨p, hp⟩
    simpa [polynomialJacobian, Pi.single_apply] using hh

theorem constant_zeroth_coordinate_of_generic_normal_separation
    [IsAlgClosed C] [Algebra.EssFiniteType C E] {m : ℕ}
    (φ : MvPolynomial (Fin (m + 1)) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥)
    (hy : φ (X (0 : Fin (m + 1))) ≠ 0)
    (hexclude : ∀ A B : Finset (Fin (m + 1)),
      IsNormalBasis (K := E)
        (fun j => (polynomialTangent φ Q).mkQ (Pi.basisFun E _ j)) A →
      IsNormalBasis (K := E)
        (fun j => (polynomialTangent φ Q).mkQ (frameBasis m (φ (X 0)) hy j)) B →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    ∃ c : C, X (0 : Fin (m + 1)) - MvPolynomial.C c ∈ Q := by
  let q := (polynomialTangent φ Q).mkQ
  have hvan : ∀ p ∈ Q, φ p = 0 := fun p hp => (hker p).mpr hp
  have hd := normal_basis_differential_dichotomy m (φ (X 0)) hy q
    (Submodule.mkQ_surjective _) (polynomialNormal_mkQ_ne_zero_of_kernel φ Q hker hQ) hexclude
  have hconst : ∃ c : C, algebraMap C E c = φ (X (0 : Fin (m + 1))) := by
    rcases hd with hzero | ⟨i, hlog⟩
    · exact constant_of_differential_eq_zero (φ (X 0))
        (differential_eq_zero_of_polynomialTangent φ Q hvan 0
          (fun t ht => hzero t ((Submodule.Quotient.mk_eq_zero _).mpr ht)))
    · exact constant_of_logarithmic_differential (φ (X i.succ)) (φ (X 0))
        (logarithmic_differential_of_polynomialTangent φ Q hvan i.succ 0
          (fun t ht => hlog t ((Submodule.Quotient.mk_eq_zero _).mpr ht)))
  obtain ⟨c, hc⟩ := hconst
  refine ⟨c, (hker _).mp ?_⟩
  simp only [map_sub, MvPolynomial.algHom_C, hc, sub_self]

end PiExponent

end

end OAI
