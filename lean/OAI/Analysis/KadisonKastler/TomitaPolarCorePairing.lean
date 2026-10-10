import OAI.Analysis.KadisonKastler.TomitaLinearPolarCoordinates

namespace OAI

/-! # The vector-state identity for polar conjugation on the algebraic core -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaCoreCoordinate_complement (a : Algebra M) :
    tomitaGraphComplementRoot (M := M) J Ω (tomitaCoreCoordinate J Ω hsep hcyc a) =
      tomitaPolarConjugation J Ω hsep hcyc (star a.val Ω) := by
  have h := tomitaCoreCoordinate_adjoint J Ω hsep hcyc a
  rw [tomitaGraphRoot_polar_symm J Ω hsep hcyc] at h
  have he := congrArg (tomitaPolarConjugation J Ω hsep hcyc) h
  rw [tomitaPolarConjugation_involutive J Ω hsep hcyc] at he
  exact he

theorem tomitaPolarConjugation_core_pairing (a b : Algebra M) :
    inner ℂ (a.val Ω) (tomitaPolarConjugation J Ω hsep hcyc (star b.val Ω)) =
      inner ℂ (tomitaPolarConjugation J Ω hsep hcyc (star a.val Ω)) (b.val Ω) := by
  let u := tomitaCoreCoordinate J Ω hsep hcyc a
  let v := tomitaCoreCoordinate J Ω hsep hcyc b
  rw [← tomitaCoreCoordinate_first J Ω hsep hcyc a,
    ← tomitaCoreCoordinate_first J Ω hsep hcyc b,
    ← tomitaCoreCoordinate_complement J Ω hsep hcyc a,
    ← tomitaCoreCoordinate_complement J Ω hsep hcyc b]
  have hr : (tomitaGraphRoot (M := M) J Ω).adjoint = tomitaGraphRoot (M := M) J Ω :=
    (tomitaGraphRoot_selfAdjoint J Ω).star_eq
  have hq : (tomitaGraphComplementRoot (M := M) J Ω).adjoint =
      tomitaGraphComplementRoot (M := M) J Ω :=
    (tomitaGraphComplementRoot_nonneg J Ω).isSelfAdjoint.star_eq
  rw [← ContinuousLinearMap.adjoint_inner_right, hr,
    ← ContinuousLinearMap.adjoint_inner_right, hq]
  exact congrArg (fun T : H →L[ℂ] H => inner ℂ u (T v))
    (tomitaGraphRoots_commute J Ω).eq

theorem tomitaPolarConjugation_vectorState (a b : Algebra M) :
    inner ℂ Ω (b.val (tomitaPolarConjugation J Ω hsep hcyc (a.val Ω))) =
      inner ℂ (a.val (tomitaPolarConjugation J Ω hsep hcyc (b.val Ω))) Ω := by
  have h := tomitaPolarConjugation_core_pairing J Ω hsep hcyc (star b) (star a)
  change inner ℂ (star b.val Ω)
      (tomitaPolarConjugation J Ω hsep hcyc (star (star a.val) Ω)) =
    inner ℂ (tomitaPolarConjugation J Ω hsep hcyc (star (star b.val) Ω))
      (star a.val Ω) at h
  rw [star_star, star_star] at h
  calc
    inner ℂ Ω (b.val (tomitaPolarConjugation J Ω hsep hcyc (a.val Ω))) =
        inner ℂ (star b.val Ω) (tomitaPolarConjugation J Ω hsep hcyc (a.val Ω)) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ (tomitaPolarConjugation J Ω hsep hcyc (b.val Ω)) (star a.val Ω) := h
    _ = inner ℂ (a.val (tomitaPolarConjugation J Ω hsep hcyc (b.val Ω))) Ω := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

end

end KadisonKastler

end OAI
