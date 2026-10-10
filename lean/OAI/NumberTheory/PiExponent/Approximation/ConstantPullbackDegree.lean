import OAI.NumberTheory.PiExponent.Approximation.LinePullback
import OAI.NumberTheory.PiExponent.Approximation.NumericalMarginRestriction
import OAI.NumberTheory.PiExponent.Approximation.SectionPullback

namespace OAI

namespace PiExponent.ConstantPullbackDegree
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

def pullbackFrame_of_range_subset (K : LineBundle Y) (g : X ⟶ Y)
    (U : Y.Opens) (h : Set.range g ⊆ (U : Set Y))
    (e : K.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    (K.pullback g).sheaf ≅ structureSheaf X := by
  have hr : Set.range g ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact h
  let l := IsOpenImmersion.lift U.ι g hr
  have hl : l ≫ U.ι = g := IsOpenImmersion.lift_fac U.ι g hr
  exact (Scheme.Modules.pullbackCongr hl.symm).app K.sheaf ≪≫
    ((Scheme.Modules.pullbackComp l U.ι).app K.sheaf).symm ≪≫
      (Scheme.Modules.pullback l).mapIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app
        K.sheaf).symm ≪≫ (Scheme.Modules.pullback l).mapIso e ≪≫ pullbackUnitIso l

def constantPullbackIso (K : LineBundle Y) (g : X ⟶ Y) (y : Y)
    (hg : Set.range g ⊆ ({y} : Set Y)) :
    (K.pullback g).sheaf ≅ structureSheaf X := by
  apply Classical.choice
  obtain ⟨U, hy, ⟨e⟩⟩ := K.locallyRankOne y
  refine ⟨pullbackFrame_of_range_subset K g U ?_ e⟩
  intro z hz
  have hz' : z = y := hg hz
  exact hz'.symm ▸ hy

theorem euler_difference_eq_zero (p : X ⟶ Spec (CommRingCat.of ℂ))
    (K : LineBundle Y) (g : X ⟶ Y) (y : Y)
    (hg : Set.range g ⊆ ({y} : Set Y)) (d : ℕ) :
    eulerCharacteristic p d (K.pullback g).sheaf -
      eulerCharacteristic p d (structureSheaf X) = 0 := by
  rw [eulerCharacteristic_iso p (constantPullbackIso K g y hg) d]
  exact sub_self _

theorem euler_difference_eq_zero_of_constant (p : X ⟶ Spec (CommRingCat.of ℂ))
    (K : LineBundle Y) (g : X ⟶ Y) (y : Y)
    (hg : ∀ x, g x = y) (d : ℕ) :
    eulerCharacteristic p d (K.pullback g).sheaf -
      eulerCharacteristic p d (structureSheaf X) = 0 :=
  euler_difference_eq_zero p K g y (by rintro z ⟨x,rfl⟩; exact hg x) d

theorem curveDegree_eq_zero_of_contracted
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (K : LineBundle Y)
    (g : X ⟶ Y) (C : NumericalAmpleness.IntegralCurve X) (y : Y)
    (hg : Set.range (C.embedding ≫ g) ⊆ ({y} : Set Y)) :
    NumericalAmpleness.curveDegree p (K.pullback g) C = 0 := by
  have he := eulerCharacteristic_iso (C.embedding ≫ p)
    ((Scheme.Modules.pullbackComp C.embedding g).app K.sheaf) 1
  simp only [CategoryTheory.Functor.comp_obj] at he
  unfold NumericalAmpleness.curveDegree
  change eulerCharacteristic (C.embedding ≫ p) 1
      ((Scheme.Modules.pullback C.embedding).obj ((Scheme.Modules.pullback g).obj K.sheaf)) -
    eulerCharacteristic (C.embedding ≫ p) 1 (structureSheaf C.scheme) = 0
  rw [he]
  exact euler_difference_eq_zero (C.embedding ≫ p) K (C.embedding ≫ g) y hg 1

end
end PiExponent.ConstantPullbackDegree

end OAI
