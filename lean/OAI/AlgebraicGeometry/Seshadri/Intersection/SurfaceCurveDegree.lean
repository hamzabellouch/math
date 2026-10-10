import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.AmpleEmbedding
import OAI.AlgebraicGeometry.Seshadri.Projective.PullbackProjective
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalDegree

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

instance IntegralCurve.proper (S : Surface) (C : IntegralCurve S) :
    IsProper (C.embedding ≫ S.structureMap) := by infer_instance

instance IntegralCurve.noetherian (S : Surface) (C : IntegralCurve S) :
    IsNoetherian C.scheme := by
  let : IsLocallyNoetherian C.scheme :=
    LocallyOfFiniteType.isLocallyNoetherian C.embedding
  let : CompactSpace C.scheme :=
    QuasiCompact.compactSpace_of_compactSpace C.embedding
  exact {}

theorem IntegralCurve.exists_projective_sections (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : LineBundle.IsAmple S.scheme A) :
    ∃ σ : Type, ∃ _ : Fintype σ, ∃ M : C.scheme.Modules,
      ∃ a : σ → (O C.scheme ⟶ M),
      ∃ ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤,
        IsClosedImmersion (sectionsMorphism (baseScalars (C.embedding ≫ S.structureMap)) a ha) := by
  obtain ⟨n,hn,σ,hσ,s,hs,hclosed⟩ := S.ample_embedding A hA
  let := hσ
  let : IsClosedImmersion (sectionsMorphism (baseScalars S.structureMap) s hs) := hclosed
  let a (i : σ) := pullbackSection C.embedding (s i)
  let ha := pullback_sections_cover s hs C.embedding
  refine ⟨σ,hσ,_,a,ha,?_⟩
  have h : C.embedding ≫ sectionsMorphism (baseScalars S.structureMap) s hs =
      sectionsMorphism (baseScalars (C.embedding ≫ S.structureMap)) a ha := by
    rw [baseScalars_comp_actual]
    exact sectionsMorphism_pullback _ s hs C.embedding
  rw [← h]
  infer_instance

theorem IntegralCurve.cohomology_finite (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : LineBundle.IsAmple S.scheme A)
    (L : LineBundle C.scheme) (n : ℕ) :
    letI := Module.compHom (cohomology L.sheaf n)
      (baseScalars (C.embedding ≫ S.structureMap))
    Module.Finite ℂ (cohomology L.sheaf n) := by
  obtain ⟨σ,hσ,M,a,ha,hc⟩ := C.exists_projective_sections S A hA
  let := hσ
  let := hc
  let : IsClosedImmersion (sectionsMorphism
    ((C.embedding ≫ S.structureMap).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) a ha) := hc
  exact projective_curve_cohomology_finite (C.embedding ≫ S.structureMap)
    C.dimension a ha L n

theorem IntegralCurve.nodal_branch_sum_le_degree (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : LineBundle.IsAmple S.scheme A)
    (L : LineBundle S.scheme) (s : O S.scheme ⟶ L.sheaf)
    (U : S.scheme.affineOpens) [Nonempty (C.embedding ⁻¹ᵁ U.1).toScheme]
    [IsDomain Γ(U.1.toScheme,⊤)]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hR : ringKrullDim Γ(U.1.toScheme,⊤) ≤ 2)
    (q : letI : Algebra ℂ Γ(U.1.toScheme,⊤) :=
        (baseScalars (U.1.ι ≫ S.structureMap)).toAlgebra
      (ℂ × ℂ) → (Γ(U.1.toScheme,⊤) →ₐ[ℂ] ℂ))
    (hq : ∀ t, AnalyticAt ℂ (fun z => q z t) 0)
    (hjets : letI : Algebra ℂ Γ(U.1.toScheme,⊤) :=
        (baseScalars (U.1.ι ≫ S.structureMap)).toAlgebra
      ∀ n : ℕ,
      RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
          (RingHom.ker (q 0))^n ∧
      Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom))
    (g : Γ(U.1.toScheme,⊤)) (hg0 : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime]
    (hker : RingHom.ker (C.embedding ∣_ U.1).appTop.hom = Ideal.span {g})
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2)
    (hf : coefficient e (restrictSection U.1.ι s) ∉ Ideal.span {g}) :
    letI : Algebra ℂ Γ(U.1.toScheme,⊤) :=
      (baseScalars (U.1.ι ≫ S.structureMap)).toAlgebra
    let f := coefficient e (restrictSection U.1.ι s)
    (((restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat : ℕ) : ℤ) ≤
      curveDegree S L C := by
  obtain ⟨σ,hσ,M,a,ha,hc⟩ := C.exists_projective_sections S A hA
  let := hσ
  let := hc
  exact actual_pullback_nodal_degree_bound S.structureMap C.embedding C.dimension
    a ha L s U e hR q hq hjets g hg0 hker u hu hu0 hg hf
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
