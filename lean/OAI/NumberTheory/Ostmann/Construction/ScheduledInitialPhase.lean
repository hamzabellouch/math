import OAI.NumberTheory.Ostmann.Construction.ScheduledPrimePhase
import OAI.NumberTheory.Ostmann.Construction.ScheduleWordUnary

namespace OAI

/-! # The initial Poisson phase is the initial phase of the actual schedule -/

namespace Ostmann

open scoped Classical

def initialSurvivorEquiv {I : Type*} (role : I → CopyScheduleRole) :
    I ≃ {i : CopyScheduleVertex I 0 // CopyScheduleSurvives role 0 i} where
  toFun i := ⟨i, trivial⟩
  invFun i := i.val
  left_inv _ := rfl
  right_inv _ := rfl

theorem initialSurvivorPrimeFact {I : Type*} (role : I → CopyScheduleRole)
    (p : I → ℕ) [hp : ∀ i, Fact (p i).Prime] :
    ∀ i : {j : CopyScheduleVertex I 0 // CopyScheduleSurvives role 0 j}, Fact (p i.val).Prime :=
  fun i => hp i.val

theorem scheduledPrimePhase_zero {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (center : ∀ p : ℕ, ZMod p) (v : ℤ) :
    letI := initialSurvivorPrimeFact role p
    scheduledPrimePhase role χ g pivot initial 0 v (fun i => p i.val) center =
      directedPrimePhase p (fun i => χ i (p i)) (fun i => center (p i))
        (fun i => initial i v (p i)) g v := by
  let := initialSurvivorPrimeFact role p
  unfold scheduledPrimePhase
  have he := directedPrimePhase_equiv (initialSurvivorEquiv role)
    (fun i => p i.val) (fun i => χ (copyScheduleOrigin 0 i.val) (p i.val))
    (fun i => center (p i.val))
    (fun i => copyScheduleUnary χ g pivot initial 0 v i.val (p i.val))
    (fun i j => copyScheduleGraph g pivot 0 i.val j.val) v
  exact he.symm

/-- The Gauss multipliers are only needed at prime arguments; their values at
other natural numbers do not enter the schedule. -/
theorem tupleGraphPhase_eq_regular_directed {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] (χ : ∀ i, DirichletCharacter ℂ (p i))
    (t : ∀ i, ZMod (p i)) (v : ℤ) :
    tupleGraphPhase p χ t v = directedPrimePhase p χ t
      (fun i => regularUnary (χ i) (primitiveGaussPhase (χ i)) 1 (v : ZMod (p i)))
      initialCompleteGraph v := by
  rw [tupleGraphPhase_eq_directed]
  have hg : (initialDirectedGraph : I → I → ℤ) = initialCompleteGraph := by
    funext i j
    rfl
  rw [hg]
  congr 1
  funext i
  simp only [regularUnary, zpow_neg_one, MulChar.inv_apply_eq_inv']

/-- The exact level-zero identification used by the initial-amplitude bound. -/
theorem tupleGraphPhase_eq_scheduled {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I)
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (center : ∀ p : ℕ, ZMod p)
    (hκ : ∀ i, κ i (p i) = primitiveGaussPhase (χ i (p i))) (v : ℤ) :
    letI := initialSurvivorPrimeFact role p
    tupleGraphPhase p (fun i => χ i (p i)) (fun i => center (p i)) v =
      scheduledPrimePhase role χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        0 v (fun i => p i.val) center := by
  let := initialSurvivorPrimeFact role p
  rw [scheduledPrimePhase_zero, tupleGraphPhase_eq_regular_directed]
  congr 1
  funext i
  simp only [initialRegularUnary, hκ]

end Ostmann

end OAI
