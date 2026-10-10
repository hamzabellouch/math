import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.AnalyticFullRank
import OAI.AlgebraicGeometry.Seshadri.Nodal.BranchDimension
import OAI.AlgebraicGeometry.Seshadri.Intersection.SectionDimension
import OAI.AlgebraicGeometry.Seshadri.Projective.OrdinaryQuadraticQuartic
import OAI.AlgebraicGeometry.Seshadri.Configurations.CenterPrime
import OAI.AlgebraicGeometry.Seshadri.Nodal.EtaleNode
import OAI.AlgebraicGeometry.Seshadri.Divisors.IntegralSectionIdeal
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorDivision
import OAI.AlgebraicGeometry.Seshadri.Nodal.FramedNodalChart

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
open MaximalSeshadri.AnalyticCoordinates
open scoped Topology

attribute [local instance] MvPolynomial.gradedAlgebra

theorem Surface.ample_integral_nodal_section_framed_etale (S : Surface)
    (L : LineBundle S.scheme) (hL : LineBundle.IsAmple S.scheme L) :
    ∃ d : ℕ, 0 < d ∧ ∃ N : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (modulePow S.scheme L.sheaf d),
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
      ∃ y : S.scheme, ∃ U : S.scheme.affineOpens, ∃ hyU : y ∈ U.1,
      ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
      ∃ _ : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ t : Fin 2 → Γ(S.scheme,U.1),
        (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale ∧
        let k := S.structureMap.appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        let _ : Algebra ℂ Γ(S.scheme, U.1) := (openScalars S.structureMap U.1).toAlgebra
        ∃ v : QuarticIndex (Fin N) → ℂ,
          (∀ x : S.scheme, x ∉ centeredOpen s ↔ x = y) ∧
          IsIntegral (doublePointQuarticIdeal k s hs v).subscheme ∧
          topologicalKrullDim (doublePointQuarticIdeal k s hs v).subscheme = 1 ∧
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
              ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V := by
  obtain ⟨d, hd, N, n, s, hs, e, y, hy, hc, hall⟩ := S.ample_quartic_integral L hL
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let := hc
  have hbase : sectionsMorphism k s hs ≫ projectiveToSpec = S.structureMap := by
    change _ ≫ projectiveBase = _
    exact (sectionsMorphism_over k s hs).trans (toSpec_scalarMap S.structureMap)
  obtain ⟨W,hyW,⟨eW⟩⟩ := L.locallyRankOne y
  obtain ⟨U, hyU, hUW, hU, i, ρ, τ, hρ, hτ, haug, hi, het, hk⟩ :=
    exists_centered_rational_jet_in_open S.structureMap k s hs hbase y ((hy y).mpr rfl) W hyW
  let : Algebra ℂ Γ(S.scheme, U.1) := (openScalars S.structureMap U.1).toAlgebra
  let a := affineSectionRatios s U hU
  let P := discriminantPolynomial a τ
  have hP : P ≠ 0 := discriminantPolynomial_ne_zero a
    (affineSectionRatios_none s U hU) τ (i 0) (i 1) (hi 0) (hi 1)
  let Q := rename e.symm P
  have hQ : Q ≠ 0 := by
    intro h
    exact hP ((MvPolynomial.renameEquiv ℂ e.symm).injective (by simpa using h))
  obtain ⟨v, hv, hint, hsm⟩ := hall Q hQ
  let f := quarticCombination a (v ∘ e.symm)
  have hf : f ∈ (RingHom.ker ρ)^2 := quarticCombination_mem_square a ρ hρ _
  have hdisc : discriminant (τ f) ≠ 0 := by
    rw [← discriminantPolynomial_eval]
    exact fun hz => hv (by simpa only [Q, P, aeval_rename] using hz)
  let : Algebra (MvPolynomial (Fin 2) ℂ) Γ(S.scheme, U.1) :=
    (eval₂Hom (openScalars S.structureMap U.1) (fun j => -a (some (i j)))).toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) Γ(S.scheme, U.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact (eval₂Hom_C (openScalars S.structureMap U.1) _ c).symm)
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) Γ(S.scheme, U.1) := het
  have hρx (j : Fin 2) : ρ (algebraMap (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) (X j)) = 0 := by
    change ρ ((eval₂Hom _ _) (X j)) = 0
    rw [eval₂Hom_X', map_neg, hρ, neg_zero]
  have hτx (j : Fin 2) : τ (algebraMap (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) (X j)) =
      Ideal.Quotient.mk _ (X j) := by
    change τ ((eval₂Hom _ _) (X j)) = _
    rw [eval₂Hom_X', map_neg, hi, neg_neg]
  obtain ⟨q,hq₀,hq,u,hu,hu₀,heq,⟨E,hE⟩,V,hV,hV₀,hinj⟩ :=
    etale_ordinary_node_realization ρ hρx τ hτ.ge hτx f hf hdisc
  have hjets := analyticTaylor_exactJets q hq E hE
  let : Nonempty U.1 := ⟨⟨y,hyU⟩⟩
  let : IsNoetherianRing Γ(S.scheme, U.1) := IsLocallyNoetherian.component_noetherian U
  have hinjective : Function.Injective (analyticTaylor q hq) :=
    exactJets_injective (q 0) (analyticTaylor q hq) (fun n => (hjets n).1)
  have hfn : f ≠ 0 := by
    intro he
    apply hdisc
    simp [he, discriminant]
  have hf0 : q 0 f = 0 := by
    rw [hq₀]
    exact (Ideal.pow_le_self (by decide : 2 ≠ 0) hf)
  have hsne : sectionCombination k (doublePointQuartics s) (v ∘ e.symm) ≠ 0 := by
    intro hz
    apply hfn
    dsimp only [f, a]
    rw [← quarticCombination_coefficient S.structureMap k s U hU hk,
      hz, restrictSection_zero, coefficient_zero, map_zero]
  have combination_eq := sectionCombination_extend_zero k (augmentedQuartics s) (v ∘ e.symm)
  have ideal_eq : (doublePointQuarticIdeal k s hs (v ∘ e.symm)).ideal U =
      Ideal.span {U.1.topIso.hom (coefficient
        (sectionFrameOn (powerSection (s none) 4) U.1
          (hU.trans (sectionOpen_le_powerSection (s none) 4)))
        (restrictSection U.1.ι
          (sectionCombination k (doublePointQuartics s) (v ∘ e.symm))))} :=
    (sectionIdeal_on_any_frame k (augmentedQuartics s) (augmentedQuartics_cover s hs)
      (fun index => index.elim 0 (v ∘ e.symm)) U
      (sectionFrameOn (powerSection (s none) 4) U.1
        (hU.trans (sectionOpen_le_powerSection (s none) 4)))).trans
      (congrArg (fun sectionValue : O S.scheme ⟶ ((L.pow d).pow 4).sheaf =>
        Ideal.span {U.1.topIso.hom (coefficient
          (sectionFrameOn (powerSection (s none) 4) U.1
            (hU.trans (sectionOpen_le_powerSection (s none) 4)))
          (restrictSection U.1.ι sectionValue))}) combination_eq)
  have hcart : InvertiblePullbackIdeal (doublePointQuarticIdeal k s hs (v ∘ e.symm))
      (𝟙 S.scheme) := by
    apply sectionIdeal_effective_cartier ((L.pow d).pow 4)
    intro zero_eq
    exact hsne (combination_eq.symm.trans zero_eq)
  have hsupport : y ∈ (doublePointQuarticIdeal k s hs (v ∘ e.symm)).support := by
    apply idealSheaf_mem_support_of_prime _ U y hyU
    rw [ideal_eq]
    rw [quarticCombination_coefficient S.structureMap k s U hU hk,
      ← centered_evaluation_kernel S.structureMap s y hy U hyU hU ρ hρ]
    apply Ideal.span_le.mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact Ideal.pow_le_self (by decide : 2 ≠ 0) hf
  let : IsIntegral (doublePointQuarticIdeal k s hs (v ∘ e.symm)).subscheme := hint
  have hprime := ideal_prime_of_integral_subscheme
    (doublePointQuarticIdeal k s hs (v ∘ e.symm)) U y hyU hsupport
  rw [ideal_eq] at hprime
  have hdim : topologicalKrullDim
      (doublePointQuarticIdeal k s hs (v ∘ e.symm)).subscheme = 1 := by
    apply le_antisymm
    · let : IsClosedImmersion (show S.scheme ⟶
          Proj (PolyGrade ℂ (Fin (S.embeddingDimension + 1))) from S.embedding) :=
        S.closedImmersion
      apply sectionIdeal_dimension_le_one S.structureMap S.embedding S.overComplex
        ((L.pow d).pow 4)
      intro zero_eq
      exact hsne (combination_eq.symm.trans zero_eq)
    · have hfp : (Ideal.span {f}).IsPrime := by
        dsimp only [f,a]
        rw [← quarticCombination_coefficient S.structureMap k s U hU hk]
        exact hprime
      let := hfp
      have hd := MaximalSeshadri.NodalLocal.nodal_principal_dimension_eq_one
        (MaximalSeshadri.EtaleDimension.etale_surface_dimension_le ℂ _)
        q hq (hjets 2).2 f hfn u hu hu₀ heq
      have H := subscheme_dimension_ge_affine_chart
        (doublePointQuarticIdeal k s hs (v ∘ e.symm)) U
      rw [ideal_eq] at H
      have he := quarticCombination_coefficient S.structureMap k s U hU hk (v ∘ e.symm)
      have dimension_eq := congrArg (fun coefficientValue : Γ(S.scheme,U.1) =>
        ringKrullDim (Γ(S.scheme,U.1) ⧸ Ideal.span {coefficientValue})) he
      exact (dimension_eq.trans hd) ▸ H
  refine ⟨d, hd, N, s, hs, y, U, hyU, hU, frameOnSmaller eW U.1 hUW, (fun j => -a (some (i j))), het, v ∘ e.symm, hy, hint, hdim, hcart, hsupport, hsne, hsm, q,
    MaximalSeshadri.EtaleDimension.etale_surface_dimension_le ℂ _, hprime, ?_, ?_, ?_,
    hq, u, hu, hu₀, ?_, ⟨i,E,?_⟩, ?_, hinjective, V,hV,hV₀,hinj⟩
  · dsimp only
    rwa [quarticCombination_coefficient S.structureMap k s U hU hk]
  · dsimp only
    rwa [quarticCombination_coefficient S.structureMap k s U hU hk]
  · rw [hq₀]
    exact centered_evaluation_kernel S.structureMap s y hy U hyU hU ρ hρ
  · dsimp only
    rw [quarticCombination_coefficient S.structureMap k s U hU hk]
    exact heq
  · simpa only [RingHom.algebraMap_toAlgebra, eval₂Hom_X'] using hE
  · intro n
    have hn := hjets n
    rw [hq₀, centered_evaluation_kernel S.structureMap s y hy U hyU hU ρ hρ] at hn
    exact hn
end
end MaximalSeshadri.Geometry

end

end OAI
