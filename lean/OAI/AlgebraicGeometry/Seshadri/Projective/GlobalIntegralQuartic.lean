import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.IntegralIdealExtension
import OAI.AlgebraicGeometry.Seshadri.Geometry.EtaleRegularPair
import OAI.AlgebraicGeometry.Seshadri.Projective.SurfaceQuartic

namespace OAI

section
noncomputable section
                                               
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.Hartogs
open MaximalSeshadri.ProjectiveBertini
attribute [local instance] MvPolynomial.gradedAlgebra

lemma center_mem_distinguished {σ : Type} {X : Scheme} {M : X.Modules}
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (p : X) (hp : p ∉ centeredOpen s) : p ∈ SectionOpens.isoOpen (s none) := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hs.ge (Set.mem_univ p))
  cases i with
  | none => exact hi
  | some i => exact (hp ((le_iSup (fun j => SectionOpens.isoOpen (s (some j))) i) hi)).elim

theorem doublePointQuartic_integral {K σ : Type} [Field K] [Fintype σ]
    {X : Scheme} [IsIntegral X] {M : X.Modules}
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)]
    (hbase : sectionsMorphism k s hs ≫ projectiveToSpec = g)
    (p : X) (hp : ∀ x : X, x ∉ centeredOpen s ↔ x = p)
    (v : QuarticIndex σ → K)
    [IsIntegral ((doublePointQuarticIdeal k s hs v).comap (centeredOpen s).ι).subscheme] :
    IsIntegral (doublePointQuarticIdeal k s hs v).subscheme := by
  have hp₀ := center_mem_distinguished s hs p ((hp p).mpr rfl)
  obtain ⟨U, hpU, hU₀, x, y, hx, hxy, hVx, hVy⟩ :=
    exists_centered_regular_pair g k s hs hbase p hp₀
  let : Nonempty U.1 := ⟨⟨p, hpU⟩⟩
  have hcover : centeredOpen s ⊔ U.1 = ⊤ := by
    apply top_unique
    intro z _
    by_cases h : z ∈ centeredOpen s
    · exact Or.inl h
    · exact Or.inr ((hp z).mp h ▸ hpU)
  have hUa : U.1 ≤ SectionOpens.isoOpen (augmentedQuartics s none) :=
    hU₀.trans (sectionOpen_le_powerSection (s none) 4)
  exact integral_ideal_of_regular_chart (doublePointQuarticIdeal k s hs v)
    (centeredOpen s) U hcover _
    (sectionIdeal_on k (augmentedQuartics s) (augmentedQuartics_cover s hs)
      (fun j => j.elim 0 v) U none hUa) x y hx hxy hVx hVy

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini

attribute [local instance] MvPolynomial.gradedAlgebra

theorem Surface.ample_quartic_integral (S : Surface)
    (L : LineBundle S.scheme) (hL : LineBundle.IsAmple S.scheme L) :
    ∃ d : ℕ, 0 < d ∧ ∃ N n : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (modulePow S.scheme L.sheaf d),
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
      ∃ e : Option (Fin n) ≃ QuarticIndex (Fin N), ∃ y : S.scheme,
        (∀ x : S.scheme, x ∉ centeredOpen s ↔ x = y) ∧
        IsClosedImmersion (sectionsMorphism
          (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) s hs) ∧
        ∀ P : MvPolynomial (Option (Fin n)) ℂ, P ≠ 0 →
          ∃ v : Option (Fin n) → ℂ, MvPolynomial.aeval v P ≠ 0 ∧
            let k := S.structureMap.appTop.hom.comp
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
            let V := centeredOpen s
            let J := doublePointQuarticIdeal k s hs (v ∘ e.symm)
            IsIntegral J.subscheme ∧
              Smooth ((J.comap V.ι).subschemeι ≫ V.ι ≫ S.structureMap) := by
  obtain ⟨d, hd, N, n, s, hs, e, y, hy, hc, hall⟩ :=
    S.ample_quartic_smooth_integral_away L hL
  let := hc
  refine ⟨d, hd, N, n, s, hs, e, y, hy, hc, ?_⟩
  intro P hP
  obtain ⟨v, hv, hi, hsm⟩ := hall P hP
  let := hi
  refine ⟨v, hv, ?_, hsm⟩
  apply doublePointQuartic_integral S.structureMap _ s hs _ y hy
  change _ ≫ projectiveBase = _
  exact (sectionsMorphism_over _ s hs).trans (toSpec_scalarMap S.structureMap)

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
