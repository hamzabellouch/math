import OAI.NumberTheory.PiExponent.Approximation.CompositePullbackFrame
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials

namespace OAI

noncomputable section
namespace PiExponent.GlobalPolynomialCoefficientLaw
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

def CoefficientLaw {Y : Scheme} {M : Y.Modules} {A : Type} [CommRing A]
    (V : Y.Opens) (e : M.restrict V.ι ≅ structureSheaf V.toScheme)
    (E : Γ(Y,V) ≃+* A) (P : (structureSheaf Y ⟶ M) → A) : Prop :=
  ∀ s, P s = E (V.topIso.hom (coefficient e (restrictSection V.ι s)))

theorem coordinate_law {Y : Scheme} {R σ : Type} [CommRing R]
    (M : Y.Modules) (s : σ → (structureSheaf Y ⟶ M)) (k : R →+* Γ(Y,⊤))
    (hc : (⨆i,PiExponentSeshadri.SectionOpens.isoOpen (s i))=⊤)
    (f : Y ≅ Proj (PolyGrade R σ)) (hf : sectionsMorphism k s hc=f.hom)
    (n : ℕ) (z : σ) :
    CoefficientLaw (PiExponentSeshadri.SectionOpens.isoOpen (s z))
      (coordinatePowerFrame (s z) n) (coordinateSectionRingEquiv M k s hc f hf z)
      (ProjectiveGlobalPolynomials.coordinateChartPolynomial M s k hc f hf n z) :=
  fun b => ProjectiveGlobalPolynomials.coordinateChartPolynomial_coefficient M s k hc f hf n z b

theorem exists_power_frame_of_law {X Y : Scheme.{0}} {A B : Type}
    [CommRing A] [CommRing B] (L : LineBundle Y) (f : X ⟶ Y)
    (φ : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion φ]
    (V : Y.Opens) (g : Spec (CommRingCat.of A) ⟶ V.toScheme)
    (hg : φ ≫ f = g ≫ V.ι) (n : ℕ)
    (e : (modulePow Y L.sheaf n).restrict V.ι ≅ structureSheaf V.toScheme)
    (E : Γ(Y,V) ≃+* B) (P : (structureSheaf Y ⟶ modulePow Y L.sheaf n) → B)
    (hP : CoefficientLaw V e E P) (ev : B →+* A)
    (hev : ∀ q, (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (g.appTop (V.topIso.inv (E.symm q))) = ev q) :
    ∃ F : (modulePow X (L.pullback f).sheaf n).restrict φ ≅ O (Spec (CommRingCat.of A)),
      ∀ s, (Scheme.ΓSpecIso (CommRingCat.of A)).hom
        (coefficient F (restrictSection φ (pullbackPowerSection L f n s))) = ev (P s) := by
  obtain ⟨F, hF⟩ := CompositePullbackFrame.exists_power_frame L f φ V g hg n e
  refine ⟨F, fun s => ?_⟩
  erw [hF s]
  have hcoef : V.topIso.inv (E.symm (P s)) = coefficient e (restrictSection V.ι s) := by
    rw [hP s, RingEquiv.symm_apply_apply]
    exact V.topIso.hom_inv_id_apply _
  rw [← hcoef]
  exact hev (P s)

end PiExponent.GlobalPolynomialCoefficientLaw
end

end OAI
