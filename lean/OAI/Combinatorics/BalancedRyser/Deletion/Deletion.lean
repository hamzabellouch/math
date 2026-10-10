import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Probability.Distributions.Poisson.Basic
import OAI.Combinatorics.BalancedRyser.Incidence.Affine

namespace OAI

open scoped NNReal

noncomputable section

namespace Balanced
open scoped _root_.Balanced

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

def IsDeletionSet (k : ℕ) (D : Finset (Line F)) : Prop :=
  ∀ d : Direction F, (D.filter fun l => l.1 = d).card = k

def DeletionSet (F : Type u) [Field F] [Fintype F] [DecidableEq F] (k : ℕ) :=
  {D : Finset (Line F) // IsDeletionSet k D}

instance (k : ℕ) : Finite (DeletionSet F k) := by
  unfold DeletionSet
  infer_instance

noncomputable instance (k : ℕ) : Fintype (DeletionSet F k) := Fintype.ofFinite _

def uncoveredBy (D : Finset (Line F)) : Finset (Point F) :=
  Finset.univ.filter fun x => ∀ l ∈ D, ¬ OnLine x l

def deletionMultiplicity (D : Finset (Line F)) (x : Point F) : ℕ :=
  (D.filter fun l => OnLine x l).card

def empiricalMultiplicityMass (D : Finset (Line F)) (n : ℕ) : ℝ :=
  ((Finset.univ.filter fun x : Point F => deletionMultiplicity D x = n).card : ℝ) /
    (Fintype.card F : ℝ) ^ 2

noncomputable def deletionPoissonMass (k n : ℕ) : ℝ :=
  (ProbabilityTheory.poissonMeasure (k : ℝ≥0)).real {n}

noncomputable def deletionMultiplicityTV (k : ℕ) (D : Finset (Line F)) : ℝ :=
  (1 / 2 : ℝ) * ∑' n : ℕ, |empiricalMultiplicityMass D n - deletionPoissonMass k n|

noncomputable def uniformDeletionMass (k : ℕ) : ℝ :=
  1 / (Fintype.card (DeletionSet F k) : ℝ)

def DeletionDominated (k : ℕ) (K : ℝ) (Q : PMF (DeletionSet F k)) : Prop :=
  ∀ D, (Q D).toReal ≤ Real.exp (K * (Fintype.card F : ℝ)) *
    uniformDeletionMass (F := F) k

noncomputable def deletionEventProbability {k : ℕ} (Q : PMF (DeletionSet F k))
    (E : DeletionSet F k → Prop) : ℝ := by
  classical
  exact ∑ D, if E D then (Q D).toReal else 0

noncomputable def deletionEventCard {k : ℕ} (E : DeletionSet F k → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter E).card

noncomputable def exceptionalOccupancyLines (k : ℕ) (lam : ℝ)
    (D : Finset (Line F)) : Finset (Line F) := by
  classical
  exact Finset.univ.filter fun l => l ∉ D ∧
    lam ≤ |(((linePoints l ∩ uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ)) -
      Real.exp (-(k : ℝ))|

def BadCoreCover (δ : ℝ) (D : Finset (Line F)) : Prop :=
  ∃ C : Finset (Line F), Disjoint C D ∧ C.card ≤ Fintype.card F ∧
    CoversPoints C (uncoveredBy D) ∧
    δ * (Fintype.card F : ℝ) ^ 2 ≤ ((uncoveredBy C).card : ℝ)

def UniformDeletionVanishing (k : ℕ) (K : ℝ)
    (E : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      N ≤ Fintype.card F → k ≤ Fintype.card F →
      ∀ Q : PMF (DeletionSet F k), DeletionDominated k K Q →
        deletionEventProbability Q (E F) < ε

def RobustDeletionResult : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ K : ℝ, 0 ≤ K →
    (∀ τ : ℝ, 0 < τ → UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val)) ∧
    (∀ lam η : ℝ, 0 < lam → 0 < η → UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ))) ∧
    (∀ δ : ℝ, 0 < δ → UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => BadCoreCover δ D.val))

end Balanced

end

end OAI
