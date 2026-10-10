import OAI.NumberTheory.Ostmann.Construction.DirectedPhaseQuotient
import OAI.NumberTheory.Ostmann.Construction.ScheduledFullFinalPermutation

namespace OAI

/-! # The literal full scheduled phase quotient at a common root -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

noncomputable def scheduledSurvivorGraph {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (i j : CopyScheduleAtoms role n) : ℤ :=
  copyScheduleGraph initialCompleteGraph pivot n i.val j.val

noncomputable def scheduledSurvivorUnary {I : Type*}
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n : ℕ) (t : FrequencyTree ℤ n)
    (i : CopyScheduleAtoms role n) (p : ℕ) : ℂ :=
  copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ) n t i.val p

theorem scheduledSamplePhase_invariant_pair {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n : ℕ) (t t' : FrequencyTree ℤ n)
    (hroot : frequencyRoot n t = frequencyRoot n t')
    (e : Equiv.Perm (CopyScheduleAtoms role n))
    (hχ : ∀ i, χ (copyScheduleOrigin n (e i).val) = χ (copyScheduleOrigin n i.val))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (q : CopyScheduleAtoms role n → P)
    (hq : Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)))
    (center : ∀ p : ℕ, ZMod p) :
    scheduledSamplePhase role χ κ pivot n t P hP q center *
      conj (scheduledSamplePhase role χ κ pivot n t' P hP (fun i => q (e i)) center) =
      finiteEdgeWeight
        (dirichletGraphEdge (fun i => χ (copyScheduleOrigin n i.val))
          (graphDifference (scheduledSurvivorGraph role pivot n)
            (transportGraph e (scheduledSurvivorGraph role pivot n))))
        (fun i p => scheduledSurvivorUnary role χ κ pivot n t i p *
          conj (scheduledSurvivorUnary role χ κ pivot n t' (e.symm i) p))
        (fun i => (q i : ℕ)) := by
  unfold scheduledSamplePhase scheduledPrimePhase
  dsimp only
  rw [← hroot]
  exact directedPrimePhase_invariant_pair (fun i => (q i : ℕ))
    (fun i => (hP _ (q i).property).ne_zero) e
    (fun i => χ (copyScheduleOrigin n i.val)) hχ center
    (scheduledSurvivorUnary role χ κ pivot n t)
    (scheduledSurvivorUnary role χ κ pivot n t')
    (scheduledSurvivorGraph role pivot n) (scheduledSurvivorGraph role pivot n)
    (frequencyRoot n t) hq
    (fun i => copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self n i.val)
    (fun i => copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self n i.val)

end Ostmann

end OAI
