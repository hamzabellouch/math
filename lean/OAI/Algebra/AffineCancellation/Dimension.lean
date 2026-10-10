import OAI.Algebra.AffineCancellation.Cylinder

namespace OAI

noncomputable section

namespace ComplexCancellation

theorem finiteType : Algebra.FiniteType ℂ A := inferInstance

instance domain : IsDomain A :=
  Function.Injective.isDomain Cylinder.coefficientMap (by
    intro r s hrs
    apply Polynomial.C_injective
    apply Cylinder.equivalence.injective
    simpa only [Cylinder.equivalence, AlgEquiv.ofAlgHom_apply,
      Cylinder.forward_C] using hrs)

instance noetherian : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A

theorem dimension : ringKrullDim A = 4 := by
  have hd : ringKrullDim A + 1 = 5 := by
    rw [← Polynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_of_ringEquiv Cylinder.equivalence.toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add]
    simp
  generalize ringKrullDim A = d at *
  induction d using WithBot.recBotCoe with
  | bot => simp at hd
  | coe d =>
    have hd' : d + 1 = 5 := WithBot.coe_inj.mp (by
      simpa only [WithBot.coe_add, WithBot.coe_one, WithBot.coe_ofNat] using hd)
    induction d using ENat.recTopCoe with
    | top => simp at hd'
    | coe n =>
      have hd'' : n + 1 = 5 := by exact_mod_cast hd'
      have hn : n = 4 := by omega
      subst n
      rfl

theorem stabilization : Nonempty (Polynomial A ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ) :=
  ⟨Cylinder.equivalence⟩

end ComplexCancellation

end

end OAI
