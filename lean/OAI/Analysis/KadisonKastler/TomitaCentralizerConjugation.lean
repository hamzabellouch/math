import OAI.Analysis.KadisonKastler.TomitaCentralizerGraph
import OAI.Analysis.KadisonKastler.TomitaPolarResolventSymmetry

namespace OAI

/-! # The exact centralizer-vector identity for the constructed conjugation -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem tomitaPolarCoordinates_centralizer (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (r : Algebra M)
    (hr : ∀ a : Algebra M,
      inner ℂ Ω ((r.val * a.val) Ω) = inner ℂ Ω ((a.val * r.val) Ω)) :
    (Real.sqrt (1 / 2) : ℂ) • (tomitaPolarCoordinates J Ω hsep hcyc (r.val Ω)).val =
      (1 / 2 : ℂ) • rescaledGraphVector J Ω 1 r.val := by
  have h := tomitaPolarCoordinates_root J Ω hsep hcyc (r.val Ω)
  rw [tomitaGraphRoot_half_eigen J Ω (r.val Ω) (graphResolvent_centralizer J Ω r hr),
    map_smul] at h
  have he := congrArg (fun v : rescaledGraphSubspace M J Ω 1 => v.val) h
  rw [tomitaGraphFirst_adjoint_apply, rescaledGraphProjection_centralizer J Ω r hr] at he
  exact he

/-- On centralizer vectors the polar conjugation is precisely adjoint. -/
theorem tomitaPolarConjugation_centralizer (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (r : Algebra M)
    (hr : ∀ a : Algebra M,
      inner ℂ Ω ((r.val * a.val) Ω) = inner ℂ Ω ((a.val * r.val) Ω)) :
    tomitaPolarConjugation J Ω hsep hcyc (r.val Ω) = star r.val Ω := by
  let U := tomitaPolarCoordinates J Ω hsep hcyc
  let k : ℂ := Real.sqrt (1 / 2)
  have hk : k ≠ 0 := by
    change (Real.sqrt (1 / 2) : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 1 / 2)))
  have hks : (starRingEnd ℂ) k = k := Complex.conj_ofReal _
  have hh : (starRingEnd ℂ) (1 / 2) = (1 / 2 : ℂ) := by
    change star (1 / 2 : ℂ) = _
    simp
  apply U.injective
  rw [tomitaPolarCoordinates_conjugation]
  apply Subtype.ext
  apply smul_right_injective (M := TomitaGraphHilbert H) hk
  change k • tomitaGraphFlip J (U (r.val Ω)).val = k • (U (star r.val Ω)).val
  calc
    k • tomitaGraphFlip J (U (r.val Ω)).val =
        tomitaGraphFlip J (k • (U (r.val Ω)).val) := by
      rw [(tomitaGraphFlip J).map_smulₛₗ, hks]
    _ = tomitaGraphFlip J ((1 / 2 : ℂ) • rescaledGraphVector J Ω 1 r.val) := by
      rw [tomitaPolarCoordinates_centralizer J Ω hsep hcyc r hr]
    _ = (1 / 2 : ℂ) • rescaledGraphVector J Ω 1 (star r.val) := by
      rw [(tomitaGraphFlip J).map_smulₛₗ, hh, tomitaGraphFlip_vector J Ω r]
    _ = k • (U (star r.val Ω)).val := by
      exact (tomitaPolarCoordinates_centralizer J Ω hsep hcyc (star r)
        (vectorState_centralizer_star Ω r hr)).symm

/-- Modular conjugation agrees with the adjoint on centralizer vectors. -/
theorem tomitaPolarConjugation_star_centralizer (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (r : Algebra M)
    (hr : ∀ a : Algebra M,
      inner ℂ Ω ((r.val * a.val) Ω) = inner ℂ Ω ((a.val * r.val) Ω)) :
    tomitaPolarConjugation J Ω hsep hcyc (star r.val Ω) = r.val Ω := by
  have h := tomitaPolarConjugation_centralizer J Ω hsep hcyc (star r)
    (vectorState_centralizer_star Ω r hr)
  change tomitaPolarConjugation J Ω hsep hcyc (star r.val Ω) = star (star r.val) Ω at h
  simpa only [star_star] using h

end

end KadisonKastler

end OAI
