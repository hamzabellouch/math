import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HorseshoeSyzygySequence
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ProjectiveTowerExactness

namespace OAI

/-! # Three compatible projective towers resolving a short exact sequence -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def horseshoeStage (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    ℕ → {T : ShortComplex (Rep.{0} ℤ G) // T.ShortExact}
  | 0 => ⟨S, hS⟩
  | n + 1 =>
    let t := horseshoeStage S hS n
    ⟨horseshoeSyzygySequence t.1 t.2, horseshoeSyzygySequence_shortExact t.1 t.2⟩

def horseshoeLeftTower (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    IntegralProjectiveTower G where
  obj n := (horseshoeStage S hS n).1.X₁
  projectiveObj n := normalizedFreeRepresentation (horseshoeStage S hS n).1.X₁
  projective _n := inferInstance
  ι n := kernel.ι (normalizedFreeAugmentation (horseshoeStage S hS n).1.X₁)
  π n := normalizedFreeAugmentation (horseshoeStage S hS n).1.X₁
  zero _n := kernel.condition _
  shortExact _n := normalizedSyzygySequence_shortExact _

def horseshoeMiddleTower (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    IntegralProjectiveTower G where
  obj n := (horseshoeStage S hS n).1.X₂
  projectiveObj n := horseshoeCover (horseshoeStage S hS n).1
  projective _n := inferInstance
  ι n := kernel.ι (horseshoeAugmentation (horseshoeStage S hS n).1 (horseshoeStage S hS n).2)
  π n := horseshoeAugmentation (horseshoeStage S hS n).1 (horseshoeStage S hS n).2
  zero _n := kernel.condition _
  shortExact n := {
    exact := ShortComplex.exact_kernel _
    mono_f := by
      change Mono (kernel.ι (horseshoeAugmentation
        (horseshoeStage S hS n).1 (horseshoeStage S hS n).2))
      infer_instance
    epi_g := inferInstance }

def horseshoeRightTower (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    IntegralProjectiveTower G where
  obj n := (horseshoeStage S hS n).1.X₃
  projectiveObj n := normalizedFreeRepresentation (horseshoeStage S hS n).1.X₃
  projective _n := inferInstance
  ι n := kernel.ι (normalizedFreeAugmentation (horseshoeStage S hS n).1.X₃)
  π n := normalizedFreeAugmentation (horseshoeStage S hS n).1.X₃
  zero _n := kernel.condition _
  shortExact _n := normalizedSyzygySequence_shortExact _

def horseshoeTowerInl (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    IntegralProjectiveTower.Map (horseshoeLeftTower S hS) (horseshoeMiddleTower S hS) where
  app n := (horseshoeStage S hS n).1.f
  cover n := horseshoeInl (horseshoeStage S hS n).1
  comm_left _n := horseshoeKernelInl_ι _ _
  comm_right _n := horseshoeInl_augmentation _ _

def horseshoeTowerSnd (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    IntegralProjectiveTower.Map (horseshoeMiddleTower S hS) (horseshoeRightTower S hS) where
  app n := (horseshoeStage S hS n).1.g
  cover n := horseshoeSnd (horseshoeStage S hS n).1
  comm_left _n := horseshoeKernelSnd_ι _ _
  comm_right _n := (horseshoeAugmentation_g _ _).symm

theorem horseshoeTower_zero (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) (n : ℕ) :
    (horseshoeTowerInl S hS).app n ≫ (horseshoeTowerSnd S hS).app n = 0 :=
  (horseshoeStage S hS n).1.zero

theorem horseshoeTower_shortExact (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk ((horseshoeTowerInl S hS).app n) ((horseshoeTowerSnd S hS).app n)
      (horseshoeTower_zero S hS n)).ShortExact :=
  (horseshoeStage S hS n).2

end PolycyclicRecognition

end

end OAI
