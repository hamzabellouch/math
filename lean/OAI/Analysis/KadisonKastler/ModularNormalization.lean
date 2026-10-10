import OAI.Analysis.KadisonKastler.ModularOrbitCommutant

namespace OAI

/-! # Normalization by the constructed modular group -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularOrbit_mem {a : H →L[ℂ] H} (ha : a ∈ M) (t : ℝ) :
    modularOrbit J Ω hsep hcyc a t ∈ M := by
  let C := tomitaPolarConjugation J Ω hsep hcyc
  have hC := tomitaPolarConjugation_involutive J Ω hsep hcyc
  have hb : conjugationOperator C a ∈ M.commutant := by
    rw [← tomitaPolarConjugation_commutant_eq J Ω hsep hcyc]
    exact ⟨a, ha, rfl⟩
  have h := modularOrbit_polar_commutant_mem J Ω hsep hcyc
    ⟨conjugationOperator C a, hb⟩ t
  change modularOrbit J Ω hsep hcyc (conjugationOperator C (conjugationOperator C a)) t ∈ M at h
  rw [conjugationOperator_twice C hC] at h
  exact h

theorem modularStrongGroup_conj_mem (s : ℝ) {a : H →L[ℂ] H} (ha : a ∈ M) :
    unitaryConj (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd s)) a ∈ M := by
  have h := modularOrbit_mem J Ω hsep hcyc ha (-s)
  simpa only [modularOrbit, neg_neg, unitaryConj, ← Unitary.coe_star,
    regularGroup_star_eq] using h

theorem modularStrongGroup_normalizes (t : Multiplicative ℝ) :
    Conjugates (modularStrongGroup J Ω hsep hcyc t) M M := by
  change unitaryConj (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t.toAdd)) ''
    (M : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H))
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact modularStrongGroup_conj_mem J Ω hsep hcyc t.toAdd hb
  · intro ha
    have h := modularStrongGroup_conj_mem J Ω hsep hcyc (-t.toAdd) ha
    rw [← regularGroup_star_eq] at h
    refine ⟨_, h, ?_⟩
    simpa only [star_star] using unitaryConj_star_unitaryConj
      (star (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t.toAdd))) a

end

end KadisonKastler

end OAI
