import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties
import OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedIntersectionCycles

namespace OAI

namespace PiExponentJets.W22

open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {k σ : Type u} [Field k] [Fintype σ]

def RetainedMinimalPrime (I T : Ideal (MvPolynomial σ k)) :=
  {Q : Ideal (MvPolynomial σ k) // Q ∈ I.minimalPrimes ∧ Q ≤ T}

namespace RetainedMinimalPrime

variable {I T : Ideal (MvPolynomial σ k)}

noncomputable instance finiteFamily (I T : Ideal (MvPolynomial σ k)) :
    Fintype (RetainedMinimalPrime I T) := by
  have hfinite : {Q : Ideal (MvPolynomial σ k) | Q ∈ I.minimalPrimes ∧ Q ≤ T}.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial σ k) I).subset
      (fun _ h => h.1)
  exact hfinite.fintype

instance (Q : RetainedMinimalPrime I T) : Q.val.IsPrime := Q.property.1.1.1

noncomputable def toComponent
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (v : σ) (hv : MvPolynomial.X v ∉ T) (Q : RetainedMinimalPrime I T) :
    ProjectiveComponent k σ :=
  ⟨Q.val, Q.property.1.1.1,
    PiExponentSiegel.W17.ConeLocalLength.minimalPrime_isHomogeneous I Q.val hI Q.property.1,
    v, fun h => hv (Q.property.2 h)⟩

omit [Fintype σ] in
@[simp] theorem toComponent_val
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (v : σ) (hv : MvPolynomial.X v ∉ T) (Q : RetainedMinimalPrime I T) :
    (toComponent hI v hv Q).val = Q.val := rfl

omit [Fintype σ] in
theorem toComponent_injective
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (v : σ) (hv : MvPolynomial.X v ∉ T) :
    Function.Injective (toComponent hI v hv : RetainedMinimalPrime I T → ProjectiveComponent k σ) := by
  intro Q R h
  exact Subtype.ext (congrArg (fun P : ProjectiveComponent k σ => P.val) h)

end RetainedMinimalPrime

namespace RetainedPrimeCycle

noncomputable def canonicalRetainedCut
    (C : RetainedPrimeCycle.{u,u,u} k σ)
    (f : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d)
    (havoid : ∀ a, f ∉ (C.component a).val)
    (s : ℕ) (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (hchildDim : ∀ a
      (Q : RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T),
      ringKrullDim (MvPolynomial σ k ⧸ Q.val) = (s+1 : ℕ)) : ProperCut C where
  polynomial := f
  polynomialDegree := d
  positiveDegree := hd
  homogeneous := hf
  avoidsParent := havoid
  dimensionIndex := s
  parentDegree := hparent
  Child := fun a => RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T
  finiteChild := fun _ => inferInstance
  child := fun a => RetainedMinimalPrime.toComponent
    (primeCut_isHomogeneous _ (C.component a).homogeneous f hf) v hv
  distinctChild := fun a => RetainedMinimalPrime.toComponent_injective
    (primeCut_isHomogeneous _ (C.component a).homogeneous f hf) v hv
  minimalChild := fun _ Q => Q.property.1
  childDegree := fun a Q => actualHP_natDegree_of_prime_dimension Q.val
    (RetainedMinimalPrime.toComponent
      (primeCut_isHomogeneous _ (C.component a).homogeneous f hf) v hv Q).homogeneous
    v (fun h => hv (Q.property.2 h)) s (hchildDim a Q)

theorem canonicalRetainedCut_covers
    (C : RetainedPrimeCycle.{u,u,u} k σ)
    (f : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d)
    (havoid : ∀ a, f ∉ (C.component a).val)
    (s : ℕ) (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (hchildDim : ∀ a
      (Q : RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T),
      ringKrullDim (MvPolynomial σ k ⧸ Q.val) = (s+1 : ℕ)) :
    (canonicalRetainedCut C f d hd hf havoid s hparent T v hv hchildDim).CoversBelow T := by
  intro a Q hQ hQT
  exact ⟨⟨Q, hQ, hQT⟩, rfl⟩

theorem canonicalRetainedCut_next_le_target
    (C : RetainedPrimeCycle.{u,u,u} k σ)
    (f : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d)
    (havoid : ∀ a, f ∉ (C.component a).val)
    (s : ℕ) (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (hchildDim : ∀ a
      (Q : RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T),
      ringKrullDim (MvPolynomial σ k ⧸ Q.val) = (s+1 : ℕ)) :
    ∀ x, ((canonicalRetainedCut C f d hd hf havoid s hparent T v hv hchildDim).next.component x).val ≤ T := by
  intro x
  exact x.2.property.2

end RetainedPrimeCycle
end PiExponentJets.W22

end OAI
