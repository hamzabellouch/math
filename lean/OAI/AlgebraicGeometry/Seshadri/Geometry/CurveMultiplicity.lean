import Mathlib
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.ClosedStalk
import OAI.AlgebraicGeometry.Seshadri.Configurations.AffinePointParameters

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma ideal_le_order_power {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) :
    I ≤ IsLocalRing.maximalIdeal R ^ idealOrder I := by
  by_cases h : idealOrder I = 0
  · simp [h]
  · by_contra hn
    have hh : idealOrder I - 1 ∈ {n : ℕ | ¬ I ≤ IsLocalRing.maximalIdeal R^(n+1)} := by
      simpa only [Set.mem_ofPred_eq,Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h)] using hn
    have := Nat.sInf_le hh
    change idealOrder I ≤ idealOrder I-1 at this
    omega

theorem IntegralCurve.affine_ideal_le_multiplicity (S : Surface) (C : IntegralCurve S)
    (U : S.scheme.affineOpens)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) :
    C.embedding.ker.ideal U ≤
      (RingHom.ker ρ) ^ curveMultiplicity S C (affineComplexPoint S.structureMap U ρ) := by
  classical
  let := (openScalars S.structureMap U.1).toAlgebra
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  let p : ComplexPoint S := affineComplexPoint S.structureMap U ρ
  change C.embedding.ker.ideal U ≤ (RingHom.ker ρ)^curveMultiplicity S C p
  unfold curveMultiplicity
  split_ifs with h
  · let q := h.choose
    have hq : C.embedding q = p.image := h.choose_spec
    have hpU : p.image ∈ U.1 := by
      have H := Set.mem_range_self (f := U.2.fromSpec) (⟨RingHom.ker ρ, RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(S.scheme,U.1))
      rw [U.2.range_fromSpec] at H
      exact H
    have hqu : C.embedding q ∈ U.1 := hq ▸ hpU
    let : Algebra Γ(S.scheme,U.1) (S.scheme.presheaf.stalk (C.embedding q)) :=
      TopCat.Presheaf.algebra_section_stalk S.scheme.presheaf ⟨C.embedding q,hqu⟩
    have hp : RingHom.ker ρ = (U.2.isoSpec.hom ⟨C.embedding q,hqu⟩).asIdeal := by
      change (⟨RingHom.ker ρ, RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(S.scheme,U.1)).asIdeal = _
      apply congrArg PrimeSpectrum.asIdeal
      apply U.2.fromSpec.isOpenEmbedding.injective
      change p.image = U.2.fromSpec (U.2.isoSpec.hom ⟨C.embedding q,hqu⟩)
      exact hq.symm.trans (congrArg
        (fun morphism : U.1.toScheme ⟶ S.scheme => morphism ⟨C.embedding q,hqu⟩)
        U.2.isoSpec_hom_fromSpec).symm
    let : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun z => ⟨algebraMap ℂ _ z,ρ.commutes z⟩)
    have : (U.2.isoSpec.hom ⟨C.embedding q,hqu⟩).asIdeal.IsPrime :=
      (U.2.isoSpec.hom ⟨C.embedding q,hqu⟩).isPrime
    let : IsLocalization.AtPrime (S.scheme.presheaf.stalk (C.embedding q)) (RingHom.ker ρ) := by
      change IsLocalization (RingHom.ker ρ).primeCompl _
      have he : (RingHom.ker ρ).primeCompl = (U.2.isoSpec.hom ⟨C.embedding q,hqu⟩).asIdeal.primeCompl := by
        ext a
        simp only [Ideal.mem_primeCompl_iff,hp]
      rw [he]
      exact U.2.isLocalization_stalk ⟨C.embedding q,hqu⟩
    have H := ideal_le_order_power (RingHom.ker (C.embedding.stalkMap q).hom)
    conv_lhs at H => rw [closedImmersion_stalk_kernel C.embedding U q hqu]
    rw [Ideal.map_le_iff_le_comap] at H
    have E := IsLocalization.AtPrime.under_maximalIdeal_pow (RingHom.ker ρ)
      (S.scheme.presheaf.stalk (C.embedding q))
      (idealOrder (RingHom.ker (C.embedding.stalkMap q).hom))
    change C.embedding.ker.ideal U ≤
      (IsLocalRing.maximalIdeal (S.scheme.presheaf.stalk (C.embedding q))^
        idealOrder (RingHom.ker (C.embedding.stalkMap q).hom)).under Γ(S.scheme,U.1) at H
    rw [E] at H
    exact H
  · simp

end
end MaximalSeshadri.Geometry

end

end OAI
