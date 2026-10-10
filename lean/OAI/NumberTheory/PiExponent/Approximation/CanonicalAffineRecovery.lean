import OAI.NumberTheory.PiExponent.Geometry.CanonicalRecoveryProperties
import OAI.NumberTheory.PiExponent.LocalAlgebra.AffineIdealSections
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction
import OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso

namespace OAI

noncomputable section
namespace PiExponent.CanonicalAffineRecovery
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule PiExponentSeshadri.IdealPullback
open GeometrySupport

private theorem bijective_iff_of_square {A B C D : Type*}
    (p : A → B) (q : C → D) (a : A → C) (b : B → D)
    (ha : Function.Bijective a) (hb : Function.Bijective b)
    (h : ∀ x, b (p x) = q (a x)) : Function.Bijective p ↔ Function.Bijective q := by
  have he : b ∘ p = q ∘ a := funext h
  rw [← hb.of_comp_iff' p, he]
  exact Function.Bijective.of_comp_iff q ha

theorem bijective_iff_comap {R : Type} [CommRing R] {Y : Scheme.{0}}
    (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (L : LineBundle Y) (ι : L.sheaf ⟶ structureSheaf Y)
    (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
    (r : I → Γ(L.sheaf,⊤))
    (hr : ∀ a : I, ι.app ⊤ (r a) =
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a.val)) :
    Function.Bijective r ↔
      Function.Bijective ((IdealPullbackMap.comap f (specIdeal I)).app ⊤) := by
  let t := PresentedIdealIso.toIdealModule (specIdeal I) f L ι hL
  have ht : Function.Bijective (t.app ⊤) := ConcreteCategory.bijective_of_isIso _
  have hdiag (a : I) :
      t.app ⊤ (r a) =
        IdealSectionRestriction.pullback f (specIdeal I) ⊤ ⊤ (by simp)
          ((AffineIdealSections.equiv I).symm a) := by
    apply IdealSectionRestriction.inclusion_injective ((specIdeal I).comap f) ⊤
    have h₁ := congrArg (fun g => g.app ⊤ (r a))
      (PresentedIdealIso.toIdealModule_inclusion (specIdeal I) f L ι hL)
    have h₂ := IdealSectionRestriction.pullback_inclusion f (specIdeal I) ⊤ ⊤
      (by simp) ((AffineIdealSections.equiv I).symm a)
    have htop : f.appLE ⊤ ⊤ (by simp) = f.appTop := f.appLE_eq_app
    rw [htop] at h₂
    have h₃ := AffineIdealSections.equiv_symm_inclusion I a
    exact (h₁.trans (hr a)).trans
      ((congrArg f.appTop h₃).symm.trans h₂.symm)
  exact (bijective_iff_of_square r
    (IdealSectionRestriction.pullback f (specIdeal I) ⊤ ⊤ (by simp))
    (AffineIdealSections.equiv I).symm (t.app ⊤)
    (AffineIdealSections.equiv I).symm.bijective ht hdiag).trans
      (IdealSectionRestriction.pullback_bijective_iff_comap f (specIdeal I) ⊤ ⊤
        (by simp) (by simp))

theorem power_bijective_iff_comap {R : Type} [CommRing R] {Y : Scheme.{0}}
    (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (L : LineBundle Y) (ι : L.sheaf ⟶ structureSheaf Y)
    (hL : PresentsPullbackIdeal (specIdeal I) f L ι) (n : ℕ)
    (r : ↥(I^n : Ideal R) → Γ((L.pow n).sheaf,⊤))
    (hr : ∀ a : ↥(I^n : Ideal R), (idealPowerInclusion L ι n).app ⊤ (r a) =
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a.val)) :
    Function.Bijective r ↔ CanonicalRecoveryProperties.ComapBijective f (specIdeal (I^n)) ⊤ := by
  have hp : PresentsPullbackIdeal (specIdeal (I^n)) f (L.pow n) (idealPowerInclusion L ι n) := by
    rw [specIdeal_pow]
    exact PresentedIdealIso.idealPower_presents (specIdeal I) f L ι hL n
  exact bijective_iff_comap (I^n) f (L.pow n) (idealPowerInclusion L ι n) hp r hr

end PiExponent.CanonicalAffineRecovery

end

end OAI
