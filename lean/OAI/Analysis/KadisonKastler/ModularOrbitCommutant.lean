import OAI.Analysis.KadisonKastler.ModularOrbitAverage
import OAI.Analysis.KadisonKastler.ModularBoundedEquation
import OAI.Analysis.KadisonKastler.PolarCommutantEquality

namespace OAI

/-! # Modular orbits of polar-conjugated commutant elements

The bounded equation and strip-average separation give the inclusion on
every orbit. The reverse inclusion is the previously proved polar duality.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularOrbit_polar_commutant_selfAdjoint_mem (b : Algebra M.commutant)
    (hb : IsSelfAdjoint b) (t : ℝ) :
    modularOrbit J Ω hsep hcyc
      (conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) b.val) t ∈ M := by
  let Y := conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) b.val
  apply mem_of_strip_averages M Real.pi_pos (modularOrbit J Ω hsep hcyc Y)
    (modularOrbit_continuous J Ω hsep hcyc Y) ‖Y‖ (modularOrbit_norm_le J Ω hsep hcyc Y) _ t
  intro φ hφ
  let z := Complex.exp (Complex.I * φ / 2)
  have hz : 0 < z.re := by
    have hcos : 0 < Real.cos (φ / 2) := Real.cos_pos_of_mem_Ioo
      ⟨by have := (abs_lt.mp hφ).1; linarith,
        by have := (abs_lt.mp hφ).2; linarith⟩
    simpa [z, Complex.exp_re] using hcos
  have hzs : star z = Complex.exp (-(Complex.I * φ / 2)) := by
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
    have harg : (starRingEnd ℂ) (Complex.I * φ / 2) = -(Complex.I * φ / 2) := by
      calc
        _ = (-Complex.I) * (φ : ℂ) / 2 := by
          rw [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, htwo]
        _ = _ := by ring
    exact (Complex.exp_conj (Complex.I * φ / 2)).symm.trans (congrArg Complex.exp harg)
  obtain ⟨x, _, _, hx⟩ := modular_bounded_equation J Ω hsep hcyc b hb z hz
  have hav := modularOrbitAverage_eq_of_equation J Ω hsep hcyc x.val Y φ hφ (by
    change _ = _ at hx ⊢
    rw [hzs] at hx
    exact hx.trans (add_comm _ _))
  change modularOrbitAverage J Ω hsep hcyc Y φ hφ ∈ M
  rw [hav]
  exact x.property

theorem modularOrbit_polar_commutant_mem (b : Algebra M.commutant) (t : ℝ) :
    modularOrbit J Ω hsep hcyc
      (conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) b.val) t ∈ M := by
  have hr := modularOrbit_polar_commutant_selfAdjoint_mem J Ω hsep hcyc
    (realPart b).val (realPart b).property t
  have hi := modularOrbit_polar_commutant_selfAdjoint_mem J Ω hsep hcyc
    (imaginaryPart b).val (imaginaryPart b).property t
  have hb : b.val = (realPart b).val.val + Complex.I • (imaginaryPart b).val.val :=
    (congrArg Subtype.val (realPart_add_I_smul_imaginaryPart b)).symm
  rw [hb, conjugationOperator_add, conjugationOperator_smul]
  change _ ∈ M
  have hs : modularOrbit J Ω hsep hcyc
      (conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) (realPart b).val.val) t +
      star Complex.I • modularOrbit J Ω hsep hcyc
        (conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) (imaginaryPart b).val.val) t ∈ M :=
    M.add_mem hr (M.smul_mem hi (star Complex.I))
  simpa only [modularOrbit, mul_add, add_mul, mul_smul_comm, smul_mul_assoc] using hs

theorem tomitaPolarConjugation_commutant_eq :
    conjugateRightAlgebra (tomitaPolarConjugation J Ω hsep hcyc)
      (tomitaPolarConjugation_involutive J Ω hsep hcyc) M = M.commutant := by
  apply tomitaPolarConjugation_commutant_eq_of_inclusion J Ω hsep hcyc
  intro b
  have h := modularOrbit_polar_commutant_mem J Ω hsep hcyc b 0
  simpa only [modularOrbit, neg_zero, show Multiplicative.ofAdd (0 : ℝ) = 1 from rfl,
    map_one, OneMemClass.coe_one, one_mul, mul_one] using h

end

end KadisonKastler

end OAI
