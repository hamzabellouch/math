import OAI.Analysis.KadisonKastler.TomitaPolarResolventSymmetry

namespace OAI

/-! # Bounded graph coordinates for algebraic Tomita vectors

Every algebra vector is the image of a concrete vector under the square
root of the graph resolvent. Its adjoint vector uses the polar conjugate
of the same coordinate. These are the two boundary data for the KMS strip.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

def tomitaCoreCoordinate (a : Algebra M) : H :=
  (tomitaPolarCoordinates J Ω hsep hcyc).symm
    ⟨rescaledGraphVector J Ω 1 a.val, rescaledGraphVector_mem M J Ω 1 a⟩

theorem tomitaCoreCoordinate_graph (a : Algebra M) :
    (tomitaPolarCoordinates J Ω hsep hcyc (tomitaCoreCoordinate J Ω hsep hcyc a)).val =
      rescaledGraphVector J Ω 1 a.val := by
  exact congrArg (fun v : rescaledGraphSubspace M J Ω 1 => v.val)
    ((tomitaPolarCoordinates J Ω hsep hcyc).apply_symm_apply _)

theorem tomitaCoreCoordinate_first (a : Algebra M) :
    tomitaGraphRoot (M := M) J Ω (tomitaCoreCoordinate J Ω hsep hcyc a) = a.val Ω := by
  have h := congrArg (fun v : TomitaGraphHilbert H => v 0)
    (tomitaCoreCoordinate_graph J Ω hsep hcyc a)
  rw [tomitaPolarCoordinates_first] at h
  exact h

theorem tomitaCoreCoordinate_adjoint (a : Algebra M) :
    tomitaGraphRoot (M := M) J Ω
      (tomitaPolarConjugation J Ω hsep hcyc (tomitaCoreCoordinate J Ω hsep hcyc a)) =
        star a.val Ω := by
  have h := congrArg (fun v : TomitaGraphHilbert H => v 1)
    (tomitaCoreCoordinate_graph J Ω hsep hcyc a)
  rw [tomitaPolarCoordinates_second] at h
  apply J.injective
  simpa only [rescaledGraphVector_one, one_smul] using h

theorem tomitaCoreCoordinate_star (a : Algebra M) :
    tomitaCoreCoordinate J Ω hsep hcyc (star a) =
      tomitaPolarConjugation J Ω hsep hcyc (tomitaCoreCoordinate J Ω hsep hcyc a) := by
  apply (tomitaPolarCoordinates J Ω hsep hcyc).injective
  apply Subtype.ext
  rw [tomitaPolarCoordinates_conjugation]
  change (tomitaPolarCoordinates J Ω hsep hcyc (tomitaCoreCoordinate J Ω hsep hcyc (star a))).val =
    tomitaGraphFlip J (tomitaPolarCoordinates J Ω hsep hcyc (tomitaCoreCoordinate J Ω hsep hcyc a)).val
  rw [tomitaCoreCoordinate_graph, tomitaCoreCoordinate_graph, tomitaGraphFlip_vector J Ω a]
  rfl

end

end KadisonKastler

end OAI
