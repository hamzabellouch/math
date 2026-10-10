import OAI.Analysis.KadisonKastler.ModularPairingOperator

namespace OAI

/-! # Constructed solutions to the bounded modular operator equation -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem modular_bounded_equation (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (b : Algebra M.commutant) (hb : IsSelfAdjoint b) (z : ℂ) (hz : 0 < z.re) :
    ∃ x : Algebra M, IsSelfAdjoint x ∧ ‖x‖ ≤ (1 + ‖b‖) / z.re ∧
      tomitaMiddleOperator (M := M) J Ω *
          conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) b.val *
          tomitaMiddleOperator (M := M) J Ω =
        star z • ((1 - graphResolvent M J Ω 1) * x.val * graphResolvent M J Ω 1) +
          z • (graphResolvent M J Ω 1 * x.val * (1 - graphResolvent M J Ω 1)) := by
  obtain ⟨x, hx, hxn, hxp⟩ := modular_radon_nikodym_selfAdjoint Ω b hb z hz
  let a : Algebra M := (1 / 2 : ℝ) • x
  have ha : IsSelfAdjoint a := by
    change star ((1 / 2 : ℝ) • x) = (1 / 2 : ℝ) • x
    rw [star_smul, star_trivial, hx.star_eq]
  refine ⟨a, ha, ?_, ?_⟩
  · change ‖(1 / 2 : ℝ) • x‖ ≤ (1 + ‖b‖) / z.re
    rw [norm_smul]
    norm_num
    have hn : ‖x‖ ≤ 2 * ((1 + ‖b‖) / z.re) := by
      convert hxn using 1
      ring
    change ‖x.val‖ ≤ 2 * ((1 + ‖b.val‖) / z.re) at hn
    linarith
  · have he := modular_pairing_operator J Ω hsep hcyc b.val b.property
      (congrArg Subtype.val hb.star_eq) z x hx hxp
    have ha' : a.val = (1 / 2 : ℂ) • x.val := by
      change (1 / 2 : ℝ) • x.val = (1 / 2 : ℂ) • x.val
      rw [← Complex.coe_smul]
      norm_num
    have hh := congrArg (fun A : H →L[ℂ] H => (1 / 2 : ℂ) • A) he
    rw [smul_smul] at hh
    norm_num at hh
    rw [ha']
    simpa only [smul_add, mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm, starRingEnd_apply] using hh

end

end KadisonKastler

end OAI
