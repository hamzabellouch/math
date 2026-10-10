import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.OpenChartDegree
import OAI.AlgebraicGeometry.Seshadri.Divisors.IntegralSectionIdeal

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Projective MaximalSeshadri.Frames
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

def IntegralCurve.ofIdeal (S : Surface) (I : S.scheme.IdealSheafData)
    [IsIntegral I.subscheme] (hd : topologicalKrullDim I.subscheme = 1) : IntegralCurve S :=
  ⟨I.subscheme,I.subschemeι,inferInstance,inferInstance,hd⟩

theorem nodal_ideal_branch_sum_le_degree (S : Surface)
    (A : LineBundle S.scheme) (hA : LineBundle.IsAmple S.scheme A)
    (I : S.scheme.IdealSheafData) [IsIntegral I.subscheme]
    (hd : topologicalKrullDim I.subscheme = 1)
    (L : LineBundle S.scheme) (s : O S.scheme ⟶ L.sheaf)
    (U : S.scheme.affineOpens) (y : S.scheme) (hyU : y ∈ U.1) (hyI : y ∈ I.support)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hR : ringKrullDim Γ(S.scheme,U.1) ≤ 2)
    (q : letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
      (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ))
    (hq : ∀ t, AnalyticAt ℂ (fun z => q z t) 0)
    (hjets : letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
      ∀ n : ℕ,
      RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
          (RingHom.ker (q 0))^n ∧
      Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom))
    (g : Γ(S.scheme,U.1)) (hg0 : g ≠ 0)
    (hI : I.ideal U = Ideal.span {g})
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2)
    (hf : U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) ∉ Ideal.span {g}) :
    letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
    let f := U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))
    (((restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat : ℕ) : ℤ) ≤
      curveDegree S L (IntegralCurve.ofIdeal S I hd) := by
  let : Nonempty U.1 := ⟨⟨y,hyU⟩⟩
  let hgp : (Ideal.span {g}).IsPrime := by
    rw [← hI]
    exact ideal_prime_of_integral_subscheme I U y hyU hyI
  have hy : y ∈ Set.range I.subschemeι := by rwa [I.range_subschemeι]
  obtain ⟨z,hz⟩ := hy
  let : Nonempty (I.subschemeι ⁻¹ᵁ U.1).toScheme :=
    ⟨⟨z,by change I.subschemeι z ∈ U.1; rwa [hz]⟩⟩
  let : Nonempty ((IntegralCurve.ofIdeal S I hd).embedding ⁻¹ᵁ U.1).toScheme :=
    inferInstanceAs (Nonempty (I.subschemeι ⁻¹ᵁ U.1).toScheme)
  have hker : RingHom.ker (I.subschemeι.app U.1).hom = Ideal.span {g} :=
    (I.ker_subschemeι_app U).trans hI
  exact (IntegralCurve.ofIdeal S I hd).nodal_branch_sum_le_degree_on_open
    S A hA L s U e hR q hq hjets g hg0 hker u hu hu0 hg hf

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
