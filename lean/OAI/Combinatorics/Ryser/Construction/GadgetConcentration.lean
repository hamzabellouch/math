import OAI.Combinatorics.Ryser.Probability.Concentration
import OAI.Combinatorics.Ryser.Probability.Product
import Mathlib.Data.Fintype.EquivFin

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable (I Ω : Type*) [Fintype I]

def finCoordinateEquiv : (Fin (Fintype.card I) → Ω) ≃ (I → Ω) where
  toFun w i := w (Fintype.equivFin I i)
  invFun a j := a ((Fintype.equivFin I).symm j)
  left_inv w := by
    funext j
    simp
  right_inv a := by
    funext i
    simp

theorem finCoordinateEquiv_update [DecidableEq I]
    (w : Fin (Fintype.card I) → Ω) (j : Fin (Fintype.card I)) (x : Ω) :
    finCoordinateEquiv I Ω (Function.update w j x) =
      Function.update (finCoordinateEquiv I Ω w) ((Fintype.equivFin I).symm j) x := by
  funext i
  change Function.update w j x (Fintype.equivFin I i) =
    Function.update (fun i => w (Fintype.equivFin I i)) ((Fintype.equivFin I).symm j) x i
  by_cases hi : i = (Fintype.equivFin I).symm j
  · subst i
    simp
  · have hij : Fintype.equivFin I i ≠ j := by
      intro h
      apply hi
      have h' := congrArg (Fintype.equivFin I).symm h
      simpa only [Equiv.symm_apply_apply] using h'
    simp [Function.update, hi, hij]

variable {I Ω} [DecidableEq I] [Fintype Ω] [Nonempty Ω]

theorem uniform_coordinate_concentration
    (f : (I → Ω) → ℝ) (c M V u : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
    (hcoord : ∀ i w x, |f (Function.update w i x) - f w| ≤ c)
    (hcM : c ≤ M) (hcV : (Fintype.card I : ℝ) * c ^ 2 ≤ V) :
    (FiniteLaw.uniform (I → Ω)).prob
        (fun w => u ≤ |f w - (FiniteLaw.uniform (I → Ω)).expectation f|) ≤
      2 * Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M)) := by
  have hcoord' : ∀ (j : Fin (Fintype.card I)) (w : Fin (Fintype.card I) → Ω) x,
      |f (finCoordinateEquiv I Ω (Function.update w j x)) -
        f (finCoordinateEquiv I Ω w)| ≤ c := by
    intro j w x
    rw [finCoordinateEquiv_update]
    exact hcoord _ _ _
  have h := Concentration.coordinate_concentration (Fintype.card I)
    (fun _ => FiniteLaw.uniform Ω) (fun w => f (finCoordinateEquiv I Ω w))
    (fun _ => c) M V u hM hV hu hcoord' (fun _ => hcM) (by simpa using hcV)
  have hmean :
      (FiniteLaw.pi (fun _ : Fin (Fintype.card I) => FiniteLaw.uniform Ω)).expectation
        (fun w => f (finCoordinateEquiv I Ω w)) =
      (FiniteLaw.uniform (I → Ω)).expectation f := by
    rw [FiniteLaw.pi_uniform]
    calc
      _ = ((FiniteLaw.uniform (Fin (Fintype.card I) → Ω)).map
          (finCoordinateEquiv I Ω)).expectation f :=
        (FiniteLaw.expectation_map _ _ _).symm
      _ = _ := by rw [FiniteLaw.map_uniform_equiv]
  rw [hmean, FiniteLaw.pi_uniform] at h
  have hprob :
      (FiniteLaw.uniform (Fin (Fintype.card I) → Ω)).prob
        (fun w => u ≤ |f (finCoordinateEquiv I Ω w) -
          (FiniteLaw.uniform (I → Ω)).expectation f|) =
      (FiniteLaw.uniform (I → Ω)).prob
        (fun w => u ≤ |f w - (FiniteLaw.uniform (I → Ω)).expectation f|) := by
    calc
      _ = ((FiniteLaw.uniform (Fin (Fintype.card I) → Ω)).map
          (finCoordinateEquiv I Ω)).prob
          (fun w => u ≤ |f w - (FiniteLaw.uniform (I → Ω)).expectation f|) :=
        (FiniteLaw.prob_map _ _ _).symm
      _ = _ := by rw [FiniteLaw.map_uniform_equiv]
  rw [hprob] at h
  exact h

end RyserCoveringCounterexample.Construction

end

end OAI
