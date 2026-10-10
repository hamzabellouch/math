import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.CenteredRationalJet

namespace OAI

section
noncomputable section
                                                  
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme} {M : X.Modules}

lemma quarticCombination_coefficient
    (g : X ⟶ Spec (CommRingCat.of K)) (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (U : X.affineOpens)
    (hU : U.1 ≤ SectionOpens.isoOpen (s none))
    (hk : ∀ c : K, U.1.topIso.hom (U.1.ι.appTop (k c)) = openScalars g U.1 c)
    (v : QuarticIndex σ → K) :
    let _ : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
    U.1.topIso.hom (coefficient
      (sectionFrameOn (powerSection (s none) 4) U.1
        (hU.trans (sectionOpen_le_powerSection (s none) 4)))
      (restrictSection U.1.ι (sectionCombination k (doublePointQuartics s) v))) =
      quarticCombination (affineSectionRatios s U hU) v := by
  let : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
  simp only [sectionCombination, restrictSection_sum, coefficient_sum,
    map_sum, coefficient_restrict_scalar_comp, map_mul, hk]
  unfold quarticCombination
  apply Finset.sum_congr rfl
  intro j hj
  rw [doublePointQuartics, quarticSection_normalized (s none) _ _ _ _ U.1 hU]
  simp only [map_mul, affineSectionRatios, quarticValue, Algebra.smul_def,
    RingHom.algebraMap_toAlgebra]

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets

attribute [local instance] MvPolynomial.gradedAlgebra

theorem Surface.ample_quartic_ordinary_quadratic (S : Surface)
    (L : LineBundle S.scheme) (hL : LineBundle.IsAmple S.scheme L) :
    ∃ d : ℕ, 0 < d ∧ ∃ N : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (modulePow S.scheme L.sheaf d),
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
      ∃ y : S.scheme, ∃ U : S.scheme.affineOpens, y ∈ U.1 ∧
      ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
        let k := S.structureMap.appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        let _ : Algebra ℂ Γ(S.scheme, U.1) := (openScalars S.structureMap U.1).toAlgebra
        ∃ ρ : Γ(S.scheme, U.1) →ₐ[ℂ] ℂ,
        ∃ τ : Γ(S.scheme, U.1) →ₐ[ℂ] JetAlgebra (Fin 2) ℂ 3,
        ∃ v : QuarticIndex (Fin N) → ℂ,
          (∀ x : S.scheme, x ∉ centeredOpen s ↔ x = y) ∧
          IsIntegral (doublePointQuarticIdeal k s hs v).subscheme ∧
          Smooth (((doublePointQuarticIdeal k s hs v).comap (centeredOpen s).ι).subschemeι ≫
            (centeredOpen s).ι ≫ S.structureMap) ∧
          RingHom.ker τ = (RingHom.ker ρ)^3 ∧
          (∀ f, jetAugment 3 (by decide) (τ f) = ρ f) ∧
          let f := U.1.topIso.hom (coefficient
            (sectionFrameOn (powerSection (s none) 4) U.1
              (hU.trans (sectionOpen_le_powerSection (s none) 4)))
            (restrictSection U.1.ι (sectionCombination k (doublePointQuartics s) v)))
          f ∈ (RingHom.ker ρ)^2 ∧ discriminant (τ f) ≠ 0 := by
  obtain ⟨d, hd, N, n, s, hs, e, y, hy, hc, hall⟩ := S.ample_quartic_integral L hL
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let := hc
  have hbase : sectionsMorphism k s hs ≫ projectiveToSpec = S.structureMap := by
    change _ ≫ projectiveBase = _
    exact (sectionsMorphism_over _ s hs).trans (toSpec_scalarMap S.structureMap)
  obtain ⟨U, hyU, hU, i, ρ, τ, hρ, hτ, haug, hi, het, hk⟩ :=
    exists_centered_rational_jet S.structureMap k s hs hbase y ((hy y).mpr rfl)
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
  refine ⟨d, hd, N, s, hs, y, U, hyU, hU, ρ, τ, v ∘ e.symm,
    hy, hint, hsm, hτ, haug, ?_⟩
  dsimp only
  rw [quarticCombination_coefficient S.structureMap k s U hU hk]
  refine ⟨quarticCombination_mem_square a ρ hρ _, ?_⟩
  rw [← discriminantPolynomial_eval]
  exact fun hz => hv (by simpa only [Q, P, aeval_rename] using hz)

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
