import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ProjectiveKernelStableMap

namespace OAI

/-! # Integral projective syzygy towers

This records the successive projective presentations used by the normalized
and horseshoe constructions. Maps lift recursively, and their induced stable
maps depend only on the stable map at the initial coefficient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

structure IntegralProjectiveTower (G : Type) [Group G] where
  obj : ℕ → Rep.{0} ℤ G
  projectiveObj : ℕ → Rep.{0} ℤ G
  projective : ∀ n, Projective (projectiveObj n)
  ι : ∀ n, obj (n + 1) ⟶ projectiveObj n
  π : ∀ n, projectiveObj n ⟶ obj n
  zero : ∀ n, ι n ≫ π n = 0
  shortExact : ∀ n, (ShortComplex.mk (ι n) (π n) (zero n)).ShortExact

namespace IntegralProjectiveTower

def sequence (T : IntegralProjectiveTower G) (n : ℕ) : ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk (T.ι n) (T.π n) (T.zero n)

instance (T : IntegralProjectiveTower G) (n : ℕ) : Projective (T.projectiveObj n) := T.projective n

instance (T : IntegralProjectiveTower G) (n : ℕ) : Projective (T.sequence n).X₂ := T.projective n

structure Map (T U : IntegralProjectiveTower G) where
  app : ∀ n, T.obj n ⟶ U.obj n
  cover : ∀ n, T.projectiveObj n ⟶ U.projectiveObj n
  comm_left : ∀ n, app (n + 1) ≫ U.ι n = T.ι n ≫ cover n
  comm_right : ∀ n, cover n ≫ U.π n = T.π n ≫ app n

namespace Map
variable {T U V : IntegralProjectiveTower G}

def sequenceMap (f : Map T U) (n : ℕ) : T.sequence n ⟶ U.sequence n where
  τ₁ := f.app (n + 1)
  τ₂ := f.cover n
  τ₃ := f.app n
  comm₁₂ := f.comm_left n
  comm₂₃ := f.comm_right n

def identity (T : IntegralProjectiveTower G) : Map T T where
  app _ := 𝟙 _
  cover _ := 𝟙 _
  comm_left _ := by rw [Category.id_comp, Category.comp_id]
  comm_right _ := by rw [Category.id_comp, Category.comp_id]

def comp (f : Map T U) (g : Map U V) : Map T V where
  app n := f.app n ≫ g.app n
  cover n := f.cover n ≫ g.cover n
  comm_left n := by
    rw [Category.assoc, g.comm_left, ← Category.assoc, f.comm_left, Category.assoc]
  comm_right n := by
    rw [Category.assoc, g.comm_right, ← Category.assoc, f.comm_right, Category.assoc]

theorem stable_eq (f g : Map T U)
    (h : stableRepresentationClass _ _ (f.app 0) = stableRepresentationClass _ _ (g.app 0))
    (n : ℕ) :
    stableRepresentationClass _ _ (f.app n) = stableRepresentationClass _ _ (g.app n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact projectiveKernelMap_stable_eq (T.shortExact n) (U.shortExact n)
      (f.sequenceMap n) (g.sequenceMap n) ih

end Map

def liftedApp (T U : IntegralProjectiveTower G) (f : T.obj 0 ⟶ U.obj 0) :
    (n : ℕ) → T.obj n ⟶ U.obj n
  | 0 => f
  | n + 1 => (projectivePresentationMap (T.sequence n) (U.sequence n)
      (T.shortExact n) (U.shortExact n) (liftedApp T U f n)).τ₁

def liftMap (T U : IntegralProjectiveTower G) (f : T.obj 0 ⟶ U.obj 0) : Map T U where
  app := liftedApp T U f
  cover n := (projectivePresentationMap (T.sequence n) (U.sequence n)
    (T.shortExact n) (U.shortExact n) (liftedApp T U f n)).τ₂
  comm_left n := (projectivePresentationMap (T.sequence n) (U.sequence n)
    (T.shortExact n) (U.shortExact n) (liftedApp T U f n)).comm₁₂
  comm_right n := (projectivePresentationMap (T.sequence n) (U.sequence n)
    (T.shortExact n) (U.shortExact n) (liftedApp T U f n)).comm₂₃

@[simp]
theorem liftMap_zero (T U : IntegralProjectiveTower G) (f : T.obj 0 ⟶ U.obj 0) :
    (liftMap T U f).app 0 = f := rfl

end IntegralProjectiveTower
end PolycyclicRecognition

end

end OAI
