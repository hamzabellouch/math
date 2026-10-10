import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionCoefficientOrder
import OAI.AlgebraicGeometry.Seshadri.Configurations.AffinePointParameters

namespace OAI


                                                
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X : Scheme.{0}}

lemma frameOnSmaller_coefficient {M : X.Modules} (U V : X.Opens) (h : V ≤ U)
    (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    coefficient (frameOnSmaller e V h) (restrictSection V.ι s) =
      (X.homOfLE h).appTop (coefficient e (restrictSection U.ι s)) := by
  unfold frameOnSmaller
  rw [coefficient_transport]
  change coefficient ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
    restrictFrame (X.homOfLE h) e) (restrictSection V.ι s ≫
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).hom.app M) = _
  rw [restrictSection_congr,coefficient_restrict_comp]

lemma affineCoefficient_restrict {M : X.Modules} (U V : X.affineOpens) (h : V.1 ≤ U.1)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme) (s : O X ⟶ M) :
    affineCoefficient V (frameOnSmaller e V.1 h) s =
      X.presheaf.map (homOfLE h).op (affineCoefficient U e s) := by
  unfold affineCoefficient
  rw [frameOnSmaller_coefficient]
  change ((X.homOfLE h).appTop ≫ V.1.topIso.hom) _ =
    (U.1.topIso.hom ≫ X.presheaf.map (homOfLE h).op) _
  exact congrArg (fun restriction : Γ(U.1.toScheme, ⊤) ⟶ Γ(X, V.1) =>
    restriction (coefficient e (restrictSection U.1.ι s)))
    (X.restrictFunctorΓ.hom.naturality (homOfLE h).op)

lemma affine_point_germ_power (g : X ⟶ complexBase) (U : X.affineOpens)
    (ρ : letI := (openScalars g U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ)
    (x : X) (hx : x ∈ U.1)
    (he : (affineComplexPoint g U ρ).left (fieldPoint ℂ) = x) (n : ℕ) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)^n).comap
      (X.presheaf.germ U.1 x hx).hom = (RingHom.ker ρ)^n := by
  let := (openScalars g U.1).toAlgebra
  let : Algebra Γ(X,U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hx⟩
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have hp : RingHom.ker ρ = (U.2.primeIdealOf ⟨x,hx⟩).asIdeal := by
    change (⟨RingHom.ker ρ,RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(X,U.1)).asIdeal = _
    apply congrArg PrimeSpectrum.asIdeal
    apply U.2.fromSpec.isOpenEmbedding.injective
    change (affineComplexPoint g U ρ).left (fieldPoint ℂ) =
      U.2.fromSpec (U.2.primeIdealOf ⟨x,hx⟩)
    exact he.trans (U.2.fromSpec_primeIdealOf ⟨x,hx⟩).symm
  let : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective _
    (fun z => ⟨algebraMap ℂ _ z,ρ.commutes z⟩)
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (RingHom.ker ρ) := by
    change IsLocalization (RingHom.ker ρ).primeCompl _
    have hpc : (RingHom.ker ρ).primeCompl = (U.2.primeIdealOf ⟨x,hx⟩).asIdeal.primeCompl := by
      ext element; simp only [Ideal.mem_primeCompl_iff,hp]
    rw [hpc]
    exact U.2.isLocalization_stalk ⟨x,hx⟩
  exact IsLocalization.AtPrime.under_maximalIdeal_pow (RingHom.ker ρ) (X.presheaf.stalk x) n

lemma affineCoefficient_order_restrict_iff (g : X ⟶ complexBase)
    {M : X.Modules} (U V : X.affineOpens) (h : V.1 ≤ U.1)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.restrict V.1.ι ≅ O V.1.toScheme)
    (ρ : letI := (openScalars g U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ)
    (σ : letI := (openScalars g V.1).toAlgebra; Γ(X,V.1) →ₐ[ℂ] ℂ)
    (he : affineComplexPoint g U ρ = affineComplexPoint g V σ)
    (s : O X ⟶ M) (n : ℕ) :
    affineCoefficient U e s ∈ (RingHom.ker ρ)^n ↔
      affineCoefficient V f s ∈ (RingHom.ker σ)^n := by
  let x := (affineComplexPoint g V σ).left (fieldPoint ℂ)
  have hx : x ∈ V.1 := by
    have H := Set.mem_range_self (f := V.2.fromSpec)
      (⟨RingHom.ker σ,RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(X,V.1))
    rw [V.2.range_fromSpec] at H
    exact H
  have hU := affine_point_germ_power g U ρ x (h hx)
    (congrArg (fun p => p.left (fieldPoint ℂ)) he) n
  have hV := affine_point_germ_power g V σ x hx rfl n
  have hass := affineCoefficient_change V (frameOnSmaller e V.1 h) f s
  rw [← Ideal.mem_iff_of_associated hass]
  rw [affineCoefficient_restrict,← hU,← hV]
  change (X.presheaf.germ U.1 x (h hx)) (affineCoefficient U e s) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)^n ↔
    (X.presheaf.germ V.1 x hx)
      (X.presheaf.map (homOfLE h).op (affineCoefficient U e s)) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)^n
  rw [TopCat.Presheaf.germ_res_apply]

end
end MaximalSeshadri.Geometry

end

end OAI
