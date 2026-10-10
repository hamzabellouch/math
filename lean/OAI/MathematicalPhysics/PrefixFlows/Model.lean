import Mathlib

namespace OAI

/-! Periodic classical solutions and material trajectories. -/

noncomputable section
open scoped ContDiff
namespace PrefixFlows
abbrev Space := Fin 3 → ℝ
abbrev Spacetime := Fin 4 → ℝ
abbrev Field := Spacetime → Space
abbrev Pressure := Spacetime → ℝ

def point (t : ℝ) (x : Space) : Spacetime := ![t, x 0, x 1, x 2]
def position (z : Spacetime) : Space := ![z 1, z 2, z 3]
def future : Set Spacetime := {z | 0 ≤ z 0}
def cylinder (T : ℝ) : Set Spacetime := {z | 0 ≤ z 0 ∧ z 0 ≤ T}
def unitCube : Set Space := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)

def axis (i : Fin 3) : Space := Pi.single i 1

def SpacePeriodic {E : Type*} (f : Spacetime → E) : Prop :=
  ∀ t, 0 ≤ t → ∀ (x : Space) (k : Fin 3 → ℤ),
    f (point t (x + fun i => (k i : ℝ))) = f (point t x)

noncomputable def spatialMean {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : Spacetime → E) (t : ℝ) : E :=
  ∫ x in unitCube, f (point t x)

def MeanZero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : Spacetime → E) : Prop :=
  ∀ t, 0 ≤ t → spatialMean f t = 0

 

structure ClassicalJet where
  dt : Field
  dx : Fin 3 → Field
  dxx : Fin 3 → Fin 3 → Field
  dp : Fin 3 → Pressure

 

def ClassicalRegularity (v : Field) (p : Pressure) (J : ClassicalJet) : Prop :=
  (∀ t, 0 ≤ t → ∀ x,
    HasDerivWithinAt (fun s => v (point s x)) (J.dt (point t x)) (Set.Ici 0) t) ∧
  (∀ t, 0 ≤ t → ∀ x i,
    HasDerivAt (fun (s : ℝ) => v (point t (x + s • axis i))) (J.dx i (point t x)) 0) ∧
  (∀ t, 0 ≤ t → ∀ x i j,
    HasDerivAt (fun (s : ℝ) => J.dx i (point t (x + s • axis j)))
      (J.dxx i j (point t x)) 0) ∧
  (∀ t, 0 ≤ t → ∀ x i,
    HasDerivAt (fun (s : ℝ) => p (point t (x + s • axis i))) (J.dp i (point t x)) 0) ∧
  (∀ T, 0 ≤ T →
    ContinuousOn v (cylinder T) ∧ ContinuousOn p (cylinder T) ∧
    ContinuousOn J.dt (cylinder T) ∧
    (∀ i, ContinuousOn (J.dx i) (cylinder T)) ∧
    (∀ i j, ContinuousOn (J.dxx i j) (cylinder T)) ∧
    (∀ i, ContinuousOn (J.dp i) (cylinder T)))

 

def ClassicalSolution (ν : ℝ) (f v : Field) (p : Pressure) : Prop :=
  SpacePeriodic v ∧ SpacePeriodic p ∧ MeanZero p ∧
  (∀ x, v (point 0 x) = 0) ∧
  ∃ J : ClassicalJet, ClassicalRegularity v p J ∧
    (∀ t, 0 ≤ t → ∀ x, ∑ i : Fin 3, J.dx i (point t x) i = 0) ∧
    (∀ t, 0 ≤ t → ∀ x,
      J.dt (point t x) +
          (∑ i : Fin 3, v (point t x) i • J.dx i (point t x)) -
          ν • (∑ i : Fin 3, J.dxx i i (point t x)) +
          (fun i => J.dp i (point t x)) = f (point t x))

def GloballySmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Spacetime → E) : Prop := ContDiffOn ℝ ∞ f future

noncomputable def kineticEnergy (v : Field) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in unitCube, ∑ i : Fin 3, (v (point t x) i) ^ 2

def BoundedEnergy (v : Field) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 ≤ t → kineticEnergy v t ≤ C

def initialLabel : Space := ![1 / 8, 1 / 4, 1 / 4]

 
def MaterialTrajectory (u : Field) (X : ℝ → Space) : Prop :=
  X 0 = initialLabel ∧ ContinuousOn X (Set.Ici 0) ∧
  ∀ t, 0 ≤ t → HasDerivWithinAt X (u (point t (X t))) (Set.Ici 0) t

 
def observed (x : Space) : Prop :=
  ∃ k : ℤ, (1 / 2 : ℝ) < x 0 - k ∧ x 0 - k < 1
end PrefixFlows
end

end OAI
