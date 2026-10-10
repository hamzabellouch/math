import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Length

namespace OAI

namespace PiExponentJets.W22

theorem length_eq_of_semilinear_bijective
    {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N]
    (σ : R →+* S) [RingHomSurjective σ]
    (f : M →ₛₗ[σ] N) (hf : Function.Bijective f) :
    Module.length R M = Module.length S N := by
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

theorem quotient_length_eq_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : J = I.map e.toRingHom) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ J) := by
  let eQ : R ⧸ I ≃+* S ⧸ J := Ideal.quotientEquiv I J e hIJ
  let f : (R ⧸ I) →ₛₗ[e.toRingHom] (S ⧸ J) :=
    { toFun := eQ
      map_add' := eQ.map_add
      map_smul' := by
        intro r x
        change eQ ((Ideal.Quotient.mk I r) * x) =
          Ideal.Quotient.mk J (e r) * eQ x
        rw [map_mul]
        change Ideal.quotientEquiv I J e hIJ (Ideal.Quotient.mk I r) * eQ x = _
        rfl }
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  exact length_eq_of_semilinear_bijective e.toRingHom f eQ.bijective

end PiExponentJets.W22

end OAI
