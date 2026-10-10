import Mathlib
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.ClosedStalk
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.IntegralCurveIdeal
import OAI.AlgebraicGeometry.Seshadri.Sheaves.AffineOrderRestriction

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma IntegralCurve.point_in_range_of_affine_ideal (S : Surface) (C : IntegralCurve S)
    (U : S.scheme.affineOpens)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ)
    (h : C.embedding.ker.ideal U ≤ RingHom.ker ρ) :
    (affineComplexPoint S.structureMap U ρ).left (fieldPoint ℂ) ∈ Set.range C.embedding := by
  let q : PrimeSpectrum Γ(S.scheme,U.1) := ⟨RingHom.ker ρ,RingHom.ker_isPrime _⟩
  have hh : U.2.fromSpec q ∈ (C.embedding.ker.support : Set S.scheme) ∩ U.1 := by
    rw [C.embedding.ker.coe_support_inter U,← U.2.fromSpec_image_zeroLocus]
    exact ⟨q,h,rfl⟩
  have he : (C.embedding.ker.support : Set S.scheme) = Set.range C.embedding := by
    rw [Scheme.Hom.support_ker]
    exact C.embedding.isClosedEmbedding.isClosed_range.closure_eq
  exact he ▸ hh.1

theorem IntegralCurve.affine_ideal_not_le_next_multiplicity (S : Surface)
    (C : IntegralCurve S) (U : S.scheme.affineOpens)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) :
    ¬ C.embedding.ker.ideal U ≤ (RingHom.ker ρ)^
      (curveMultiplicity S C (affineComplexPoint S.structureMap U ρ)+1) := by
  classical
  let := (openScalars S.structureMap U.1).toAlgebra
  let p : ComplexPoint S := affineComplexPoint S.structureMap U ρ
  change ¬ C.embedding.ker.ideal U ≤ (RingHom.ker ρ)^(curveMultiplicity S C p+1)
  unfold curveMultiplicity
  split_ifs with h
  · let q := h.choose
    have hq : C.embedding q = p.image := h.choose_spec
    have hpU : p.image ∈ U.1 := by
      have H := Set.mem_range_self (f := U.2.fromSpec)
        (⟨RingHom.ker ρ,RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(S.scheme,U.1))
      rw [U.2.range_fromSpec] at H
      exact H
    have hqu : C.embedding q ∈ U.1 := hq ▸ hpU
    let : Nonempty U.1 := ⟨⟨_,hpU⟩⟩
    let : Nonempty (C.embedding ⁻¹ᵁ U.1) := ⟨⟨q,hqu⟩⟩
    let : IsNoetherianRing Γ(S.scheme,U.1) := IsLocallyNoetherian.component_noetherian U
    let I := C.embedding.ker.ideal U
    have hI : I ≠ ⊥ := C.affine_ideal_ne_bot S U inferInstance
    have hf : {n : ℕ | ¬ I ≤ (RingHom.ker ρ)^(n+1)}.Nonempty := by
      by_contra hn
      have hn' (n : ℕ) : I ≤ (RingHom.ker ρ)^(n+1) := by
        by_contra hh
        exact hn ⟨n,hh⟩
      apply hI
      apply bot_unique
      intro a ha
      have hall : a ∈ (⨅ n : ℕ, (RingHom.ker ρ)^n) := by
        apply Ideal.mem_iInf.mpr
        intro n
        cases n with
        | zero => simp
        | succ n => exact hn' n ha
      rw [(RingHom.ker ρ).iInf_pow_eq_bot_of_isDomain (RingHom.ker_ne_top _)] at hall
      exact hall
    have he (n : ℕ) : RingHom.ker (C.embedding.stalkMap q).hom ≤
        IsLocalRing.maximalIdeal (S.scheme.presheaf.stalk (C.embedding q))^(n+1) ↔
        I ≤ (RingHom.ker ρ)^(n+1) := by
      rw [closedImmersion_stalk_kernel C.embedding U q hqu,Ideal.map_le_iff_le_comap]
      rw [affine_point_germ_power S.structureMap U ρ (C.embedding q) hqu hq.symm (n+1)]
    have horder : idealOrder (RingHom.ker (C.embedding.stalkMap q).hom) =
        sInf {n : ℕ | ¬ I ≤ (RingHom.ker ρ)^(n+1)} := by
      unfold idealOrder
      congr 1
      ext n
      exact not_congr (he n)
    rw [horder]
    exact Nat.sInf_mem hf
  · simp only [Nat.zero_add,pow_one]
    intro hi
    exact h (C.point_in_range_of_affine_ideal S U ρ hi)

end
end MaximalSeshadri.Geometry

end


end OAI
