import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalPrimeTower

namespace OAI

namespace PiExponentJets.W22

variable {A : Type*} [CommRing A]

def MinimalParentsBelow (I Q : Ideal A) := {P : Ideal A // P ∈ I.minimalPrimes ∧ P ≤ Q}

noncomputable instance minimalParentsBelow_fintype [IsNoetherianRing A] (I Q : Ideal A) :
    Fintype (MinimalParentsBelow I Q) := by
  have hfinite : {P : Ideal A | P ∈ I.minimalPrimes ∧ P ≤ Q}.Finite :=
    (I.finite_minimalPrimes_of_isNoetherianRing A).subset (fun _ h => h.1)
  exact hfinite.fintype

instance {I Q : Ideal A} (P : MinimalParentsBelow I Q) : P.val.IsPrime := P.property.1.1.1

noncomputable def localizedMinimalPrimesEquiv (I Q : Ideal A) [Q.IsPrime] :
    (I.map (algebraMap A (Localization.AtPrime Q))).minimalPrimes ≃ MinimalParentsBelow I Q := by
  classical
  let L := Localization.AtPrime Q
  let e := IsLocalization.AtPrime.orderIsoOfPrime L Q
  let f : (I.map (algebraMap A L)).minimalPrimes → MinimalParentsBelow I Q := fun p =>
    ⟨p.val.comap (algebraMap A L), by
      have hmin : p.val.comap (algebraMap A L) ∈ I.minimalPrimes :=
        (Set.ext_iff.mp (IsLocalization.minimalPrimes_map Q.primeCompl L I) p.val).mp p.property
      exact ⟨hmin, (e ⟨p.val, p.property.1.1⟩).property.2⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q h
    apply Subtype.ext
    apply (IsLocalization.orderEmbedding Q.primeCompl L).injective
    exact congrArg Subtype.val h
  · intro P
    let p := e.symm ⟨P.val, P.property.1.1.1, P.property.2⟩
    have heq : p.val.comap (algebraMap A L) = P.val :=
      congrArg Subtype.val (e.apply_symm_apply ⟨P.val, P.property.1.1.1, P.property.2⟩)
    have hp : p.val ∈ (I.map (algebraMap A L)).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map Q.primeCompl L I]
      change p.val.comap (algebraMap A L) ∈ I.minimalPrimes
      rw [heq]
      exact P.property.1
    exact ⟨⟨p.val, hp⟩, Subtype.ext heq⟩

@[simp] theorem localizedMinimalPrimesEquiv_apply
    (I Q : Ideal A) [Q.IsPrime]
    (p : (I.map (algebraMap A (Localization.AtPrime Q))).minimalPrimes) :
    (localizedMinimalPrimesEquiv I Q p).val =
      p.val.comap (algebraMap A (Localization.AtPrime Q)) := rfl

end PiExponentJets.W22

end OAI
