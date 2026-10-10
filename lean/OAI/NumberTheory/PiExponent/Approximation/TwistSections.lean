import OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation
import OAI.NumberTheory.PiExponent.Approximation.FrameSections

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {X : Scheme}

def moduleSectionMultiplyRight (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) : M ⟶ moduleTensor X M L :=
  (moduleTensorRightUnit M).inv ≫ moduleTensorMap (𝟙 M) s

@[reassoc] theorem moduleSectionMultiplyRight_natural {M N L : X.Modules}
    (f : M ⟶ N) (s : structureSheaf X ⟶ L) :
    f ≫ moduleSectionMultiplyRight N s =
      moduleSectionMultiplyRight M s ≫ moduleTensorMap f (𝟙 L) := by
  have h : f ≫ (moduleTensorRightUnit N).inv =
      (moduleTensorRightUnit M).inv ≫ moduleTensorMap f (𝟙 (structureSheaf X)) := by
    apply (cancel_mono (moduleTensorRightUnit N).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [moduleTensorRightUnit_natural]
    simp
  unfold moduleSectionMultiplyRight
  rw [← Category.assoc, h, Category.assoc, ← moduleTensorMap_comp,
    Category.comp_id, Category.id_comp]
  rw [Category.assoc, ← moduleTensorMap_comp]
  simp

def moduleSectionMultiplyRightNat {L : X.Modules} (s : structureSheaf X ⟶ L) :
    𝟭 X.Modules ⟶ moduleTensorRightFunctor L where
  app M := moduleSectionMultiplyRight M s
  naturality _ _ f := moduleSectionMultiplyRight_natural f s

def moduleTwistStep (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) (n : ℕ) :
    moduleTwistFunctor L n ⟶ moduleTwistFunctor L (n+1) where
  app M := moduleSectionMultiplyRight ((moduleTwistFunctor L n).obj M) s
  naturality _ _ f := moduleSectionMultiplyRight_natural ((moduleTwistFunctor L n).map f) s

def moduleTwistSection (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) :
    ∀ n : ℕ, 𝟭 X.Modules ⟶ moduleTwistFunctor L n
  | 0 => 𝟙 _
  | n+1 => moduleTwistSection L s n ≫ moduleTwistStep L s n

def moduleTwistForward (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) (n : ℕ) :
    ∀ k : ℕ, moduleTwistFunctor L n ⟶ moduleTwistFunctor L (n+k)
  | 0 => 𝟙 _
  | k+1 => moduleTwistForward L s n k ≫ moduleTwistStep L s (n+k)

@[simp] theorem moduleTwistSection_add (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (n k : ℕ) :
    moduleTwistSection L s (n+k) = moduleTwistSection L s n ≫ moduleTwistForward L s n k := by
  induction k with
  | zero => exact (Category.comp_id _).symm
  | succ k ih =>
    change moduleTwistSection L s (n+k) ≫ moduleTwistStep L s (n+k) =
      moduleTwistSection L s n ≫
        (moduleTwistForward L s n k ≫ moduleTwistStep L s (n+k))
    rw [ih, Category.assoc]

def moduleTwistRestrictFrame (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    ∀ n : ℕ, moduleTwistFunctor L n ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι
  | 0 => Iso.refl _
  | n+1 => Functor.isoWhiskerLeft (moduleTwistFunctor L n)
      (moduleTensorRestrictFrame U L.sheaf e) ≪≫ moduleTwistRestrictFrame L U e n

@[simp] theorem moduleTwistRestrictFrame_zero (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (M : X.Modules) :
    ((moduleTwistRestrictFrame L U e 0).app M).hom = 𝟙 (M.restrict U.ι) := rfl

@[simp] theorem moduleTwistRestrictFrame_succ (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (M : X.Modules) (n : ℕ) :
    ((moduleTwistRestrictFrame L U e (n+1)).app M).hom =
      ((moduleTensorRestrictFrame U L.sheaf e).app ((moduleTwistFunctor L n).obj M)).hom ≫
        ((moduleTwistRestrictFrame L U e n).app M).hom := rfl

end
end PiExponentSeshadri.Geometry

end OAI
