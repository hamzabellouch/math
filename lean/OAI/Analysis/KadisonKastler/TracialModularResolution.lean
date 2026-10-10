import OAI.Analysis.KadisonKastler.ConstructedModularData

namespace OAI

/-! # Tracial specialization of the constructed modular operators

For a tracial vector state the group is the identity on a dense algebra
orbit. Its normalization clause is therefore unconditional. The polar
conjugation acts by adjoint and gives the right multiplication operators.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))
  (htrace : ∀ a b : Algebra M,
    inner ℂ Ω ((a.val * b.val) Ω) = inner ℂ Ω ((b.val * a.val) Ω))

include htrace

/-- The polar conjugation is adjoint on every tracial algebra vector. -/
theorem tomitaPolarConjugation_tracial (a : Algebra M) :
    tomitaPolarConjugation J Ω hsep hcyc (a.val Ω) = star a.val Ω :=
  tomitaPolarConjugation_centralizer J Ω hsep hcyc a (htrace a)

/-- In the tracial case the conjugate left action is right multiplication. -/
theorem tomitaPolarConjugation_right_action (a b : Algebra M) :
    conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) a.val (b.val Ω) =
      (b.val * star a.val) Ω := by
  change tomitaPolarConjugation J Ω hsep hcyc
    (a.val (tomitaPolarConjugation J Ω hsep hcyc (b.val Ω))) = _
  rw [tomitaPolarConjugation_tracial J Ω hsep hcyc htrace b]
  have h := tomitaPolarConjugation_tracial J Ω hsep hcyc htrace (a * star b)
  change tomitaPolarConjugation J Ω hsep hcyc ((a.val * star b.val) Ω) =
    (star (a.val * star b.val)) Ω at h
  simpa only [mul_apply_eq_comp, star_mul, star_star] using h

/-- These right actions commute with the entire represented algebra. -/
theorem tomitaPolarConjugation_tracial_mem_commutant (a : Algebra M) :
    conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) a.val ∈ M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro x hx
  apply ContinuousLinearMap.ext
  intro ξ
  apply hcyc.induction_on (p := fun ξ =>
    (x * conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) a.val) ξ =
    (conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) a.val * x) ξ) ξ
  · exact isClosed_eq (x * conjugationOperator _ a.val).continuous
      (conjugationOperator _ a.val * x).continuous
  · intro b
    change x (conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) a.val (b.val Ω)) =
      conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) a.val ((x * b.val) Ω)
    rw [tomitaPolarConjugation_right_action J Ω hsep hcyc htrace a b]
    have h := tomitaPolarConjugation_right_action J Ω hsep hcyc htrace a
      (⟨x, hx⟩ * b)
    exact (congrArg x (rfl : (b.val * star a.val) Ω = b.val (star a.val Ω))).trans h.symm

variable [TopologicalSpace.SeparableSpace H]

/-- A faithful tracial cyclic representation has the trivial modular group. -/
theorem modularStrongGroup_tracial (t : Multiplicative ℝ) :
    modularStrongGroup J Ω hsep hcyc t = 1 := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro ξ
  change (modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H) ξ = ξ
  apply hcyc.induction_on (p := fun ξ =>
    (modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H) ξ = ξ) ξ
  · exact isClosed_eq (modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H).continuous continuous_id
  · intro a
    exact modularStrongGroup_fixes_centralizer_vector J Ω hsep hcyc t.toAdd a (htrace a)

def tracialModularSpectralResolution : ModularSpectralResolution M Ω :=
  constructedModularSpectralResolution J Ω hsep hcyc (fun t => by
    rw [modularStrongGroup_tracial J Ω hsep hcyc htrace t]
    exact conjugates_one M)

end

end KadisonKastler

end OAI
