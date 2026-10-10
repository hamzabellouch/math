import OAI.Analysis.KadisonKastler.TracialModularResolution

namespace OAI

/-! # The full commutant identity for a tracial cyclic vector

Adjoint on the dense algebra orbit determines adjoint on the commutant
orbit as well. Applying the right-action calculation to both algebras and
using the bicommutant identity proves equality of the conjugate algebra
and the commutant.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem conjugation_right_action_of_star_vectors
    (N : VonNeumannAlgebra H) (C : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hstar : ∀ a : Algebra N, C (a.val Ω) = star a.val Ω)
    (a b : Algebra N) :
    conjugationOperator C a.val (b.val Ω) = (b.val * star a.val) Ω := by
  change C (a.val (C (b.val Ω))) = _
  rw [hstar b]
  have h := hstar (a * star b)
  change C ((a.val * star b.val) Ω) = star (a.val * star b.val) Ω at h
  simpa only [mul_apply_eq_comp, star_mul, star_star] using h

private theorem conjugation_mem_commutant_of_star_vectors
    (N : VonNeumannAlgebra H) (C : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hcyc : DenseRange (algebraVectorMap N Ω))
    (hstar : ∀ a : Algebra N, C (a.val Ω) = star a.val Ω)
    (a : Algebra N) : conjugationOperator C a.val ∈ N.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro x hx
  apply ContinuousLinearMap.ext
  intro ξ
  apply hcyc.induction_on (p := fun ξ =>
    (x * conjugationOperator C a.val) ξ = (conjugationOperator C a.val * x) ξ) ξ
  · exact isClosed_eq (x * conjugationOperator C a.val).continuous
      (conjugationOperator C a.val * x).continuous
  · intro b
    change x (conjugationOperator C a.val (b.val Ω)) =
      conjugationOperator C a.val ((x * b.val) Ω)
    rw [conjugation_right_action_of_star_vectors N C Ω hstar a b]
    exact (conjugation_right_action_of_star_vectors N C Ω hstar a (⟨x, hx⟩ * b)).symm

private theorem conjugation_star_vectors_commutant
    (N : VonNeumannAlgebra H) (C : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hcyc : DenseRange (algebraVectorMap N Ω))
    (hstar : ∀ a : Algebra N, C (a.val Ω) = star a.val Ω)
    (r : Algebra N.commutant) : C (r.val Ω) = star r.val Ω := by
  apply ext_inner_left ℂ
  intro ξ
  apply hcyc.induction_on (p := fun ξ =>
    inner ℂ ξ (C (r.val Ω)) = inner ℂ ξ (star r.val Ω)) ξ
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · intro a
    have hCa : C (star a.val Ω) = a.val Ω := by
      simpa only [StarMemClass.coe_star, star_star] using hstar (star a)
    have hc := congrArg (fun T : H →L[ℂ] H => T Ω)
      (VonNeumannAlgebra.mem_commutant_iff.mp r.property a.val a.property)
    change a.val (r.val Ω) = r.val (a.val Ω) at hc
    calc
      inner ℂ (a.val Ω) (C (r.val Ω)) =
          inner ℂ (C (star a.val Ω)) (C (r.val Ω)) := by rw [hCa]
      _ = star (inner ℂ (star a.val Ω) (r.val Ω)) := conjugateIsometry_inner C _ _
      _ = inner ℂ (r.val Ω) (star a.val Ω) := inner_conj_symm _ _
      _ = inner ℂ (a.val (r.val Ω)) Ω := ContinuousLinearMap.adjoint_inner_right a.val _ Ω
      _ = inner ℂ (r.val (a.val Ω)) Ω := by rw [hc]
      _ = inner ℂ (a.val Ω) (star r.val Ω) :=
        (ContinuousLinearMap.adjoint_inner_right r.val _ Ω).symm

variable {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))
  (htrace : ∀ a b : Algebra M,
    inner ℂ Ω ((a.val * b.val) Ω) = inner ℂ Ω ((b.val * a.val) Ω))

include htrace

theorem tomitaPolarConjugation_tracial_commutant (r : Algebra M.commutant) :
    tomitaPolarConjugation J Ω hsep hcyc (r.val Ω) = star r.val Ω :=
  conjugation_star_vectors_commutant M _ Ω hcyc
    (tomitaPolarConjugation_tracial J Ω hsep hcyc htrace) r

/-- The exact modular commutant equality, in the tracial case. -/
theorem tomitaPolarConjugation_tracial_commutant_eq :
    conjugateRightAlgebra (tomitaPolarConjugation J Ω hsep hcyc)
      (tomitaPolarConjugation_involutive J Ω hsep hcyc) M = M.commutant := by
  apply le_antisymm
  · intro T hT
    obtain ⟨a, ha, rfl⟩ := hT
    exact tomitaPolarConjugation_tracial_mem_commutant J Ω hsep hcyc htrace ⟨a, ha⟩
  · intro T hT
    have hd : DenseRange (algebraVectorMap M.commutant Ω) :=
      Generator.commutant_orbit_dense M Ω (fun a ha => hsep ha)
    have hm := conjugation_mem_commutant_of_star_vectors M.commutant
      (tomitaPolarConjugation J Ω hsep hcyc) Ω hd
      (tomitaPolarConjugation_tracial_commutant J Ω hsep hcyc htrace) ⟨T, hT⟩
    rw [VonNeumannAlgebra.commutant_commutant] at hm
    exact ⟨conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) T, hm,
      conjugationOperator_twice _ (tomitaPolarConjugation_involutive J Ω hsep hcyc) T⟩

/-- A tracial state gives modular conjugation data. -/
def tracialModularConjugationData : ModularConjugationData M Ω :=
  constructedModularConjugationData J Ω hsep hcyc
    (tomitaPolarConjugation_tracial_commutant_eq J Ω hsep hcyc htrace)

end

end KadisonKastler

end OAI
