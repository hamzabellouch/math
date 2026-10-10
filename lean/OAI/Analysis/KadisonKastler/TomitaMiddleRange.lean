import OAI.Analysis.KadisonKastler.TomitaMiddleCore
import OAI.Analysis.KadisonKastler.ModularResolventRange

namespace OAI

/-! # Bounded algebra representatives for both adjoint commutant vectors -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem graphResolvent_commutant_starPair (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (b : Algebra M.commutant) :
    ∃ a : Algebra M,
      a.val Ω = graphResolvent M J Ω 1 (b.val Ω) ∧
      star a.val Ω = graphResolvent M J Ω 1 (star b.val Ω) := by
  obtain ⟨p, hp, _, hep⟩ := graphResolvent_commutant_selfAdjoint J Ω
    (realPart b).val (realPart b).property
  obtain ⟨q, hq, _, heq⟩ := graphResolvent_commutant_selfAdjoint J Ω
    (imaginaryPart b).val (imaginaryPart b).property
  have hb : b.val = (realPart b).val.val + Complex.I • (imaginaryPart b).val.val :=
    (congrArg Subtype.val (realPart_add_I_smul_imaginaryPart b)).symm
  have hp' : star p.val = p.val := congrArg Subtype.val hp.star_eq
  have hq' : star q.val = q.val := congrArg Subtype.val hq.star_eq
  have hbr : star (realPart b).val.val = (realPart b).val.val :=
    congrArg Subtype.val (realPart b).property.star_eq
  have hbi : star (imaginaryPart b).val.val = (imaginaryPart b).val.val :=
    congrArg Subtype.val (imaginaryPart b).property.star_eq
  refine ⟨p + Complex.I • q, ?_, ?_⟩
  · change p.val Ω + Complex.I • q.val Ω = _
    rw [hb, add_apply, smul_apply, map_add, map_smul, hep, heq]
  · change star (p.val + Complex.I • q.val) Ω = _
    rw [star_add, star_smul, hp', hq', hb, star_add, star_smul, hbr, hbi,
      add_apply, smul_apply, add_apply, smul_apply, map_add, map_smul, hep, heq]

theorem tomitaMiddle_commutant_representative (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (b : Algebra M.commutant) :
    ∃ a : Algebra M,
      a.val Ω = tomitaMiddleOperator (M := M) J Ω
        (tomitaPolarConjugation J Ω hsep hcyc (b.val Ω)) ∧
      star a.val Ω = tomitaMiddleOperator (M := M) J Ω
        (tomitaPolarConjugation J Ω hsep hcyc (star b.val Ω)) := by
  obtain ⟨a, ha, has⟩ := graphResolvent_commutant_starPair J Ω (star b)
  refine ⟨a, ?_, ?_⟩
  · rw [tomitaMiddleOperator_commutant J Ω hsep hcyc]
    exact ha
  · rw [show star b.val = (star b).val from rfl,
      tomitaMiddleOperator_commutant J Ω hsep hcyc]
    exact has

end

end KadisonKastler

end OAI
