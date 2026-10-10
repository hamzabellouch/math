import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalDivisor
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalIdealDegree
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.LocalContainment

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

attribute [local instance] MvPolynomial.gradedAlgebra

theorem Surface.ample_integral_nodal_section_with_degree (S : Surface)
    (L : LineBundle S.scheme) (hL : LineBundle.IsAmple S.scheme L) :
    ∃ d : ℕ, 0 < d ∧ ∃ N : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (modulePow S.scheme L.sheaf d),
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
      ∃ y : S.scheme, ∃ U : S.scheme.affineOpens, ∃ hyU : y ∈ U.1,
      ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
        let k := S.structureMap.appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        let _ : Algebra ℂ Γ(S.scheme, U.1) := (openScalars S.structureMap U.1).toAlgebra
        ∃ v : QuarticIndex (Fin N) → ℂ,
          (∀ x : S.scheme, x ∉ centeredOpen s ↔ x = y) ∧
          ∃ hint : IsIntegral (doublePointQuarticIdeal k s hs v).subscheme,
          ∃ hdim : topologicalKrullDim (doublePointQuarticIdeal k s hs v).subscheme = 1,
          InvertiblePullbackIdeal (doublePointQuarticIdeal k s hs v) (𝟙 S.scheme) ∧
          y ∈ (doublePointQuarticIdeal k s hs v).support ∧
          sectionCombination k (doublePointQuartics s) v ≠ 0 ∧
          Smooth (((doublePointQuarticIdeal k s hs v).comap (centeredOpen s).ι).subschemeι ≫
            (centeredOpen s).ι ≫ S.structureMap) ∧
          let f := U.1.topIso.hom (coefficient
            (sectionFrameOn (powerSection (s none) 4) U.1
              (hU.trans (sectionOpen_le_powerSection (s none) 4)))
            (restrictSection U.1.ι (sectionCombination k (doublePointQuartics s) v)))
          ∃ q : (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
            ringKrullDim Γ(S.scheme,U.1) ≤ 2 ∧ (Ideal.span {f}).IsPrime ∧
            f ≠ 0 ∧ q 0 f = 0 ∧
            RingHom.ker (q 0) = (U.2.isoSpec.hom ⟨y,hyU⟩).asIdeal ∧
            ∃ hq : (∀ a, AnalyticAt ℂ (fun z => q z a) 0),
            ∃ u : (ℂ × ℂ) → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
              (∀ᶠ z in 𝓝 0, q z f = u z*z.1*z.2) ∧
              (∃ i : Fin 2 → Fin N, ∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ),
                HasFDerivAt (fun z =>
                  (q z (-affineSectionRatios s U hU (some (i 1))),
                   q z (-affineSectionRatios s U hU (some (i 0)))))
                  (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
              (∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
                (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
                (analyticTaylor q hq).toRingHom) =
                  (U.2.isoSpec.hom ⟨y,hyU⟩).asIdeal^n ∧
                Function.Surjective ((Ideal.Quotient.mk
                  (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
                  (analyticTaylor q hq).toRingHom)) ∧
              Function.Injective (analyticTaylor q hq) ∧
              (∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V) ∧
              ∀ (B : LineBundle S.scheme) (t : O S.scheme ⟶ B.sheaf)
                (eB : B.sheaf.restrict U.1.ι ≅ O U.1.toScheme),
                pullbackSection (doublePointQuarticIdeal k s hs v).subschemeι t ≠ 0 →
                let b := U.1.topIso.hom (coefficient eB (restrictSection U.1.ι t))
                (((restrictX ℂ (bivariateTaylor q hq b)).order.toNat +
                  (restrictZ ℂ (bivariateTaylor q hq b)).order.toNat : ℕ) : ℤ) ≤
                  curveDegree S B (@IntegralCurve.ofIdeal S
                    (doublePointQuarticIdeal k s hs v) hint hdim) := by
  obtain ⟨d,hd,N,s,hs,y,U,hyU,hU,v,hy,hint,hdim,hcart,hsup,hsne,hsm,q,
    hR,hprime,hfn,hf0,hq0,hq,u,hu,hu0,hnode,hder,hjets,hinj,hV⟩ :=
    S.ample_integral_nodal_section L hL
  refine ⟨d,hd,N,s,hs,y,U,hyU,hU,v,hy,hint,hdim,hcart,hsup,hsne,hsm,q,
    hR,hprime,hfn,hf0,hq0,hq,u,hu,hu0,hnode,hder,hjets,hinj,hV,?_⟩
  intro B t eB hne
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let I := doublePointQuarticIdeal k s hs v
  let : IsIntegral I.subscheme := hint
  let : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
  let f := U.1.topIso.hom (coefficient
    (sectionFrameOn (powerSection (s none) 4) U.1
      (hU.trans (sectionOpen_le_powerSection (s none) 4)))
    (restrictSection U.1.ι (sectionCombination k (doublePointQuartics s) v)))
  have hI : I.ideal U = Ideal.span {f} := by
    change (sectionIdeal k (augmentedQuartics s) (augmentedQuartics_cover s hs)
      (fun index => index.elim 0 v)).ideal U = Ideal.span {f}
    rw [sectionIdeal_on_any_frame k _ _ _ U
      (sectionFrameOn (powerSection (s none) 4) U.1
        (hU.trans (sectionOpen_le_powerSection (s none) 4))),
      sectionCombination_extend_zero]
    rfl
  have hjets' := hjets
  rw [← hq0] at hjets'
  apply nodal_ideal_branch_sum_le_degree S L hL I hdim B t U y hyU hsup eB
    hR q hq hjets' f hfn hI u hu hu0 hnode
  intro hb
  apply hne
  have hy' : y ∈ Set.range I.subschemeι := by rw [I.range_subschemeι]; exact hsup
  obtain ⟨z,hz⟩ := hy'
  let : Nonempty (I.subschemeι ⁻¹ᵁ U.1).toScheme :=
    ⟨⟨z,by change I.subschemeι z ∈ U.1; rwa [hz]⟩⟩
  apply (pullback_section_zero_iff_local_coefficient S.structureMap I B t U eB).mpr
  rw [hI]
  exact hb

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
