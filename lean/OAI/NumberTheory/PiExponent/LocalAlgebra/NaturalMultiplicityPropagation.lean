import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedOneCutPropagation
import OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

theorem minimal_cut_of_intermediate_parent
    {A : Type*} [CommRing A] (I P Q : Ideal A) (x : A)
    (hQ : Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes) (hIP : I ≤ P) (hPQ : P ≤ Q) :
    Q ∈ (P ⊔ Ideal.span {x}).minimalPrimes := by
  refine ⟨⟨hQ.1.1, sup_le hPQ (le_sup_right.trans hQ.1.2)⟩, ?_⟩
  intro K hK hKQ
  exact hQ.2 ⟨hK.1, (sup_le_sup hIP le_rfl).trans hK.2⟩ hKQ

universe u
variable {k σ : Type u} [Field k] [Fintype σ]

omit [Fintype σ] in
theorem cut_ideal_homogeneous
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (x : MvPolynomial σ k) (hx : x.IsHomogeneous d) :
    (I ⊔ Ideal.span {x}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  simpa only [sup_comm] using primeCut_isHomogeneous I hI x hx

theorem natural_local_onecut_recurrence
    (I Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (x : MvPolynomial σ k) (hx : x.IsHomogeneous d)
    (hQ : Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes)
    (hdim : ringKrullDim (Localization.AtPrime Q ⧸
      I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) = 1)
    (hregular : Function.Injective
      (W28.LocalIntersection.quotientMul
        (I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q)))
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q) x))) :
    actualLocalLength (I ⊔ Ideal.span {x}) Q =
      ∑ P : MinimalParentsBelow I Q, actualLocalLength I P.val *
        actualLocalLength (P.val ⊔ Ideal.span {x}) Q := by
  have hrec := localized_onecut_parent_recurrence I Q x hdim hregular
  have hsum : globalParentCutSum I Q x =
      ((∑ P : MinimalParentsBelow I Q, actualLocalLength I P.val *
        actualLocalLength (P.val ⊔ Ideal.span {x}) Q : ℕ) : ℕ∞) := by
    unfold globalParentCutSum
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro P _
    have hP := PiExponentSiegel.W17.ConeLocalLength.minimalPrime_isHomogeneous
      I P.val hI P.property.1
    have hQP := minimal_cut_of_intermediate_parent I P.val Q x hQ
      P.property.1.1.2 P.property.2
    rw [actualLocalLength_spec I P.val hI P.property.1,
      actualLocalLength_spec (P.val ⊔ Ideal.span {x}) Q
        (cut_ideal_homogeneous P.val hP x hx) hQP, Nat.cast_mul]
  rw [actualLocalLength_spec (I ⊔ Ideal.span {x}) Q
    (cut_ideal_homogeneous I hI x hx) hQ, hsum] at hrec
  exact_mod_cast hrec

noncomputable def parentChildIncidenceEquiv
    (I T : Ideal (MvPolynomial σ k)) (x : MvPolynomial σ k) :
    (Σ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T, MinimalParentsBelow I Q.val) ≃
      (Σ P : RetainedMinimalPrime I T,
        {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val}) where
  toFun z := ⟨⟨z.2.val, z.2.property.1, z.2.property.2.trans z.1.property.2⟩,
    z.1, z.2.property.2⟩
  invFun z := ⟨z.2.val, z.1.val, z.1.property.1, z.2.property⟩
  left_inv := by rintro ⟨Q,P⟩; rfl
  right_inv := by rintro ⟨P,Q⟩; rfl

end PiExponentJets.W22

end OAI
