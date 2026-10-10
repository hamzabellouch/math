import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealSectionRestriction

namespace OAI

noncomputable section
namespace PiExponent.IdealSectionRestriction
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.IdealModule

private theorem bijective_iff_of_square {A B C D : Type*}
    (p : A → B) (q : C → D) (a : A → C) (b : B → D)
    (ha : Function.Bijective a) (hb : Function.Bijective b)
    (h : ∀ x, b (p x) = q (a x)) : Function.Bijective p ↔ Function.Bijective q := by
  have he : b ∘ p = q ∘ a := funext h
  rw [← hb.of_comp_iff' p, he]
  exact Function.Bijective.of_comp_iff q ha

private theorem appLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

theorem squareIdeal {X Y X' Y' : Scheme.{0}} (f : Y ⟶ X)
    (j : X' ⟶ X) (k : Y' ⟶ Y) (f' : Y' ⟶ X') (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) :
    (I.comap f).comap k = (I.comap j).comap f' := by
  rw [← I.comap_comp k f, ← I.comap_comp f' j, h]

theorem pullback_open_square {X Y X' Y' : Scheme.{0}}
    (f : Y ⟶ X) [QuasiCompact f]
    (j : X' ⟶ X) [IsOpenImmersion j]
    (k : Y' ⟶ Y) [IsOpenImmersion k]
    (f' : Y' ⟶ X') [QuasiCompact f'] (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) (U : X'.Opens) (V : Y'.Opens)
    (hV : k ''ᵁ V ≤ f ⁻¹ᵁ (j ''ᵁ U)) (hV' : V ≤ f' ⁻¹ᵁ U)
    (s : Γ(closedModule I, j ''ᵁ U)) :
    idealCongr (squareIdeal f j k f' h I) V
      (sectionsEquiv (I.comap f) k V
        (pullback f I (j ''ᵁ U) (k ''ᵁ V) hV s)) =
      pullback f' (I.comap j) U V hV' (sectionsEquiv I j U s) := by
  apply inclusion_injective ((I.comap j).comap f') V
  rw [idealCongr_inclusion]
  have h₁ := sectionsEquiv_inclusion (I.comap f) k V
    (pullback f I (j ''ᵁ U) (k ''ᵁ V) hV s)
  have h₂ := pullback_inclusion f I (j ''ᵁ U) (k ''ᵁ V) hV s
  have h₃ := pullback_inclusion f' (I.comap j) U V hV' (sectionsEquiv I j U s)
  have h₄ := sectionsEquiv_inclusion I j U s
  rw [Scheme.Hom.appIso_hom'] at h₁ h₄
  have hh : f.appLE (j ''ᵁ U) (k ''ᵁ V) hV ≫
      k.appLE (k ''ᵁ V) V (k.preimage_image_eq V).ge =
      j.appLE (j ''ᵁ U) U (j.preimage_image_eq U).ge ≫ f'.appLE U V hV' := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr h _ _ _ _
  exact (h₁.trans (congrArg (k.appLE (k ''ᵁ V) V (k.preimage_image_eq V).ge) h₂)).trans
    ((congrArg (fun a => a ((closedInclusion I).app (j ''ᵁ U) s)) hh).trans
      ((congrArg (f'.appLE U V hV') h₄).symm.trans h₃.symm))

theorem pullback_open_square_bijective_iff {X Y X' Y' : Scheme.{0}}
    (f : Y ⟶ X) [QuasiCompact f]
    (j : X' ⟶ X) [IsOpenImmersion j]
    (k : Y' ⟶ Y) [IsOpenImmersion k]
    (f' : Y' ⟶ X') [QuasiCompact f'] (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) (U : X'.Opens) (V : Y'.Opens)
    (hV : k ''ᵁ V ≤ f ⁻¹ᵁ (j ''ᵁ U)) (hV' : V ≤ f' ⁻¹ᵁ U) :
    Function.Bijective (pullback f I (j ''ᵁ U) (k ''ᵁ V) hV) ↔
      Function.Bijective (pullback f' (I.comap j) U V hV') := by
  exact bijective_iff_of_square
    (pullback f I (j ''ᵁ U) (k ''ᵁ V) hV)
    (pullback f' (I.comap j) U V hV')
    (sectionsEquiv I j U)
    (fun z => idealCongr (squareIdeal f j k f' h I) V
      (sectionsEquiv (I.comap f) k V z))
    (sectionsEquiv I j U).bijective
    ((idealCongr (squareIdeal f j k f' h I) V).bijective.comp
      (sectionsEquiv (I.comap f) k V).bijective)
    (pullback_open_square f j k f' h I U V hV hV')

theorem comap_app_bijective_iff_open_square {X Y X' Y' : Scheme.{0}}
    (f : Y ⟶ X) [QuasiCompact f]
    (j : X' ⟶ X) [IsOpenImmersion j]
    (k : Y' ⟶ Y) [IsOpenImmersion k]
    (f' : Y' ⟶ X') [QuasiCompact f'] (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) (U : X.Opens) (U' : X'.Opens) (V' : Y'.Opens)
    (hj : j ''ᵁ U' = U) (hk : k ''ᵁ V' = f ⁻¹ᵁ U)
    (hv : V' = f' ⁻¹ᵁ U') :
    Function.Bijective ((GeometrySupport.IdealPullbackMap.comap f I).app U) ↔
      Function.Bijective ((GeometrySupport.IdealPullbackMap.comap f' (I.comap j)).app U') := by
  subst U
  exact (pullback_bijective_iff_comap f I (j ''ᵁ U') (k ''ᵁ V') hk.le hk).symm.trans
    ((pullback_open_square_bijective_iff f j k f' h I U' V' hk.le hv.le).trans
      (pullback_bijective_iff_comap f' (I.comap j) U' V' hv.le hv))

end PiExponent.IdealSectionRestriction

end

end OAI
