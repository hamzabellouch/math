import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.LocalSectionDegree
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalGlobalBound
import OAI.AlgebraicGeometry.Seshadri.Intersection.QuotientIntersection

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

variable {X Y : Scheme.{0}}

theorem projective_nodal_degree_bound [IsIntegral X] [IsNoetherian X]
    {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (a : σ → (O X ⟶ M)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (i : Y ⟶ X) [IsOpenImmersion i] [IsAffine Y] [IsNoetherian Y] [Nonempty Y]
    (e : L.sheaf.restrict i ≅ O Y)
    {R : Type} [CommRing R] [Algebra ℂ R] [IsDomain R]
    (hR : ringKrullDim R ≤ 2)
    (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ)) (hq : ∀ t, AnalyticAt ℂ (fun z => q z t) 0)
    (hjets : ∀ n : ℕ,
      RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
          (RingHom.ker (q 0))^n ∧
      Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom))
    (f g : R) (hg0 : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime]
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) (hf : f ∉ Ideal.span {g})
    (π : letI : Algebra ℂ Γ(Y,⊤) := (baseScalars (i ≫ p)).toAlgebra
      R →ₐ[ℂ] Γ(Y,⊤)) (hπ : Function.Surjective π)
    (hker : letI : Algebra ℂ Γ(Y,⊤) := (baseScalars (i ≫ p)).toAlgebra
      RingHom.ker π.toRingHom = Ideal.span {g})
    (hcoeff : π f = coefficient e (restrictSection i s)) :
    (((restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat : ℕ) : ℤ) ≤
        eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) := by
  let : Algebra ℂ Γ(Y,⊤) := (baseScalars (i ≫ p)).toAlgebra
  let E := principalIntersectionEquiv π hπ g hker f
  have hfin := projective_local_section_quotient_finite p hd a ha L s hs i e
  have hb := projective_local_section_length_le_degree p hd a ha L s hs i e
  rw [← hcoeff] at hfin hb
  let : FiniteDimensional ℂ (Γ(Y,⊤) ⧸ Ideal.span {π f}) := hfin
  let : FiniteDimensional ℂ (R ⧸ Ideal.span {f,g}) :=
    FiniteDimensional.of_injective E.toLinearMap E.injective
  have hn := integral_nodal_branch_sum_le_affine hR q hq hjets f g hg0 u hu hu0 hg hf
  rw [E.toLinearEquiv.finrank_eq] at hn
  exact (Int.ofNat_le.mpr hn).trans hb
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
