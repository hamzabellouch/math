import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserDerivatives
import Mathlib.Topology.Algebra.Module.Determinant

namespace OAI

/-! The finite-dimensional ODE input used by the transport step.

Gerald Teschl, Ordinary Differential Equations and Dynamical Systems,
AMS GSM 140 (2012), Theorem 2.10, equations (2.49)--(2.51), Lemma 2.7,
and Lemma 3.11. We retain only dimension three, four spatial derivatives,
and the closed time interval [0,1]. Uniform derivative bounds follow by
applying Gronwall to the four variational equations.
-/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def flowJacobian (G : Position → ℝ → Position) (t : ℝ) (x : Position) : ℝ :=
  (fderiv ℝ (fun y => G y t) x).det

def fieldDivergence (v : Position → Position) (x : Position) : ℝ :=
  ∑ a : Fin 3, NeutralAtom.dirPartial (fun y => v y a) (NeutralAtom.axis a) x

def IsUnitTimeFlow (v : ℝ → Position → Position) (G : Position → ℝ → Position) : Prop :=
  (∀ x, G x 0 = x) ∧
    ∀ x t, t ∈ Set.Icc (0 : ℝ) 1 →
      HasDerivWithinAt (G x) (v t (G x t)) (Set.Icc (0 : ℝ) 1) t

/-- Smooth dependence, Liouville's equation and a uniform finite-order variational estimate. -/
structure PublishedC4FlowInput : Prop where
  regularity : ∀ (U : Set (ℝ × Position)), IsOpen U →
    Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set Position) ⊆ U →
    ∀ v : ℝ → Position → Position,
    ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U →
    ∀ G : Position → ℝ → Position, IsUnitTimeFlow v G →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiff ℝ 4 (fun x => G x t)) ∧
      (∀ x t, t ∈ Set.Icc (0 : ℝ) 1 →
        HasDerivWithinAt (fun s => flowJacobian G s x)
          (fieldDivergence (v t) (G x t) * flowJacobian G t x)
          (Set.Icc (0 : ℝ) 1) t)
  uniform : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 < C ∧
    ∀ (U : Set (ℝ × Position)), IsOpen U →
    Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set Position) ⊆ U →
    ∀ v : ℝ → Position → Position,
    ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U →
    (∀ r ≤ 4, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ r (fun p : ℝ × Position => v p.1 p.2) (t,x)‖ ≤ B) →
    ∀ G : Position → ℝ → Position, IsUnitTimeFlow v G →
    ∀ r : ℕ, 1 ≤ r → r ≤ 4 → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ r (fun y => G y t) x‖ ≤ C

end ContinuumCoulomb

end

end OAI
