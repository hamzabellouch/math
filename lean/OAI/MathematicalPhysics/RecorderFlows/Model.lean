import Mathlib

namespace OAI

/-! Periodic incompressible fields, classical solutions and bounded smooth forcing. -/

namespace Solenoidal
namespace Fluid
open scoped ContDiff

abbrev Space := Fin 3 → ℝ
abbrev SpaceTime := Fin 4 → ℝ
abbrev Field := SpaceTime → Space
abbrev Pressure := SpaceTime → ℝ

def point (t : ℝ) (x : Space) : SpaceTime := Fin.cons t x

def translateTime (h : ℝ) (p : SpaceTime) : SpaceTime :=
  Function.update p 0 (p 0 + h)

def translateSpace (k : Fin 3 → ℤ) (p : SpaceTime) : SpaceTime :=
  point (p 0) (fun i => p i.succ + (k i : ℝ))

def SpatiallyPeriodic {E : Type*} (F : SpaceTime → E) : Prop :=
  ∀ (p : SpaceTime) (k : Fin 3 → ℤ), F (translateSpace k p) = F p

noncomputable def partialD (i : Fin 4) (F : Field) : Field :=
  fun p => fderiv ℝ F p (Pi.single i 1)

noncomputable def mixedD : List (Fin 4) → Field → Field
  | [], F => F
  | i :: l, F => partialD i (mixedD l F)

noncomputable def diverge (F : Field) (p : SpaceTime) : ℝ :=
  ∑ i : Fin 3, partialD i.succ F p i

noncomputable def laplacian (F : Field) (p : SpaceTime) : Space :=
  ∑ i : Fin 3, partialD i.succ (partialD i.succ F) p

noncomputable def advection (F : Field) (p : SpaceTime) : Space :=
  ∑ i : Fin 3, (F p i) • partialD i.succ F p

 
noncomputable def force (ν : ℝ) (U : Field) : Field :=
  fun p => partialD 0 U p - ν • laplacian U p

 
def cell : Set Space := Set.Icc 0 (fun _ => 1)

noncomputable def spatialMean (F : Field) (t : ℝ) : Space :=
  ∫ x in cell, F (point t x)

noncomputable def pressureMean (p : Pressure) (t : ℝ) : ℝ :=
  ∫ x in cell, p (point t x)

noncomputable def energy (U : Field) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in cell, ∑ i : Fin 3, (U (point t x) i) ^ 2

 
def BoundedMixed (F : Field) : Prop :=
  ∀ a : List (Fin 4), ∃ C : ℝ, 0 ≤ C ∧
    ∀ p : SpaceTime, 0 ≤ p 0 → ‖mixedD a F p‖ ≤ C

def PeriodicAfterOne (F : Field) : Prop :=
  ∀ p : SpaceTime, 1 ≤ p 0 → F (translateTime 1 p) = F p

def ZeroNearIntegers (U f : Field) : Prop :=
  ∀ n : ℤ, ∃ ε : ℝ, 0 < ε ∧ ∀ p : SpaceTime,
    0 ≤ p 0 → |p 0 - (n : ℝ)| < ε → U p = 0 ∧ f p = 0

 

structure ClassicalSolutionOn (ν : ℝ) (f v : Field) (p : Pressure) (T : ℝ) : Prop where
  periodic_v : ∀ t ∈ Set.Icc 0 T, ∀ (x : Space) (k : Fin 3 → ℤ),
    v (point t (fun i => x i + (k i : ℝ))) = v (point t x)
  periodic_p : ∀ t ∈ Set.Icc 0 T, ∀ (x : Space) (k : Fin 3 → ℤ),
    p (point t (fun i => x i + (k i : ℝ))) = p (point t x)
  continuous_v : ContinuousOn (fun tx : ℝ × Space => v (point tx.1 tx.2))
    (Set.Icc 0 T ×ˢ Set.univ)
  continuous_p : ContinuousOn (fun tx : ℝ × Space => p (point tx.1 tx.2))
    (Set.Icc 0 T ×ˢ Set.univ)
  zero_initial : ∀ x : Space, v (point 0 x) = 0
  zero_pressure_mean : ∀ t ∈ Set.Icc 0 T, pressureMean p t = 0
  derivatives : ∃ (vTime : Field) (vSpace : Fin 3 → Field)
      (vSpace2 : Fin 3 → Fin 3 → Field) (pSpace : Fin 3 → Pressure),
    (ContinuousOn (fun tx : ℝ × Space => vTime (point tx.1 tx.2))
      (Set.Icc 0 T ×ˢ Set.univ)) ∧
    (∀ i, ContinuousOn (fun tx : ℝ × Space => vSpace i (point tx.1 tx.2))
      (Set.Icc 0 T ×ˢ Set.univ)) ∧
    (∀ i j, ContinuousOn (fun tx : ℝ × Space => vSpace2 i j (point tx.1 tx.2))
      (Set.Icc 0 T ×ˢ Set.univ)) ∧
    (∀ i, ContinuousOn (fun tx : ℝ × Space => pSpace i (point tx.1 tx.2))
      (Set.Icc 0 T ×ˢ Set.univ)) ∧
    (∀ t ∈ Set.Icc 0 T, ∀ x : Space,
      HasDerivWithinAt (fun s => v (point s x)) (vTime (point t x)) (Set.Icc 0 T) t) ∧
    (∀ i, ∀ t ∈ Set.Icc 0 T, ∀ x : Space,
      HasDerivAt (fun s : ℝ => v (point t (x + s • Pi.single i 1)))
        (vSpace i (point t x)) 0) ∧
    (∀ i j, ∀ t ∈ Set.Icc 0 T, ∀ x : Space,
      HasDerivAt (fun s : ℝ => vSpace i (point t (x + s • Pi.single j 1)))
        (vSpace2 i j (point t x)) 0) ∧
    (∀ i, ∀ t ∈ Set.Icc 0 T, ∀ x : Space,
      HasDerivAt (fun s : ℝ => p (point t (x + s • Pi.single i 1)))
        (pSpace i (point t x)) 0) ∧
    (∀ t ∈ Set.Icc 0 T, ∀ x : Space, ∑ i : Fin 3, vSpace i (point t x) i = 0) ∧
    (∀ t ∈ Set.Icc 0 T, ∀ x : Space,
      vTime (point t x) + ∑ i : Fin 3, v (point t x) i • vSpace i (point t x) =
        -(fun i => pSpace i (point t x)) +
        ν • (∑ i : Fin 3, vSpace2 i i (point t x)) + f (point t x))

 

def FluidAssertions (ν : ℝ) (U f : Field) : Prop :=
  ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ f ∧ SpatiallyPeriodic U ∧ SpatiallyPeriodic f ∧
  (∀ q : SpaceTime, 0 ≤ q 0 → diverge f q = 0) ∧
  (∀ t : ℝ, 0 ≤ t → spatialMean f t = 0) ∧
  (∀ q : SpaceTime, 0 ≤ q 0 →
    partialD 0 U q + advection U q = ν • laplacian U q + f q) ∧
  (∀ q : SpaceTime, 0 ≤ q 0 → diverge U q = 0) ∧
  (∀ x : Space, U (point 0 x) = 0) ∧
  (∀ T : ℝ, 0 < T → ∀ (v : Field) (p : Pressure), ClassicalSolutionOn ν f v p T →
    ∀ t ∈ Set.Icc 0 T, ∀ x : Space, v (point t x) = U (point t x) ∧ p (point t x) = 0)

def BoundedPeriodicAssertions (U f : Field) : Prop :=
  BoundedMixed U ∧ BoundedMixed f ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → energy U t ≤ C) ∧
  PeriodicAfterOne U ∧ PeriodicAfterOne f ∧ ZeroNearIntegers U f
end Fluid
end Solenoidal

end OAI
