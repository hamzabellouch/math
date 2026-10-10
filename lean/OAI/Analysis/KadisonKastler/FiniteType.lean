import OAI.Analysis.KadisonKastler.TypeIInjectivity
import OAI.Analysis.KadisonKastler.FiniteOperatorAlgebra
import OAI.Analysis.KadisonKastler.PublishedFiniteType
import OAI.Analysis.KadisonKastler.TypeIFactorStability

namespace OAI

/-! # Discharging preservation of the finite diffuse type

A finite type I factor is finite dimensional. A nearby II₁ factor would
then be finite dimensional as well, contradicting its projection splitting.
Thus its finite neighboring factor is diffuse.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem IsTypeIFactor.finiteDimensional {M : VonNeumannAlgebra H}
    (hM : IsTypeIFactor M)
    (hfinite : ∀ v : Algebra M, star v * v = 1 → v * star v = 1) :
    FiniteDimensional ℂ (Algebra M) := by
  obtain ⟨p, hp⟩ := hM.minimal
  obtain ⟨ξ, hξ, hpξ⟩ := exists_nonzero_fixed_vector p hp.1
  let K := typeICyclicSpace M ξ
  let e : Algebra M ≃⋆ₐ[ℂ] (K →L[ℂ] K) :=
    typeICyclicEquiv hM.factor p hp ξ hξ hpξ
  let f : (K →L[ℂ] K) →⋆ₐ[ℂ] Algebra M := e.symm.toStarAlgHom
  let g : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K) := e.toStarAlgHom
  have : FiniteDimensional ℂ K := by
    apply finiteDimensional_of_all_isometries_coisometric
    intro v hv
    have hpre : star (f v) * f v = 1 := by
      rw [← map_star, ← map_mul, hv, map_one]
    have hh := congrArg g (hfinite (f v) hpre)
    have hgf : g (f v) = v := e.apply_symm_apply v
    simpa only [map_mul, map_star, hgf, map_one] using hh
  exact FiniteDimensional.of_injective e.toAlgEquiv.toLinearMap e.injective

/-- The finite-neighbor type input follows from the constructed type I
representation and the elementary finite-dimensional gap argument. -/
theorem publishedFiniteType : PublishedFiniteType (H := H) := by
  intro M N _ hM hgap
  obtain ⟨hcenter, hfinite⟩ := finite_factor_of_near_II1 hM hgap
  have hN : ScalarCenter N := by
    intro x hx hcomm
    obtain ⟨z, hz⟩ := hcenter ⟨x, hx⟩ (fun a => Subtype.ext (hcomm a.val a.property))
    exact ⟨z, congrArg Subtype.val hz⟩
  by_cases htype : IsTypeIFactor N
  · have := htype.finiteDimensional hfinite
    exact False.elim ((not_finiteDimensional_of_isII1Factor M hM)
      (finiteDimensional_of_near_finiteDimensional M N hgap))
  · exact (isTypeIFactor_or_projectionDiffuse hN).resolve_left htype

end

end KadisonKastler

end OAI
