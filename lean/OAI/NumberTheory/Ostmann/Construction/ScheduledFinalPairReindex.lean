import OAI.NumberTheory.Ostmann.Construction.ScheduledFullMatchingGraph
import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalComparison

namespace OAI

/-! # Reindexing two actual final arrangements to their relative matching -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

noncomputable def scheduledFinalRelativePerm {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e f : FinalParityReassignments n m) : Equiv.Perm (CopyScheduleAtoms role (n + 1)) :=
  (scheduledFullFinalPerm role n m word f).trans (scheduledFullFinalPerm role n m word e).symm

theorem scheduledFinalRelativePerm_matching {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word}) (e f : FinalParityReassignments n m) :
    scheduledFinalRelativePerm role n m word e f =
      scheduledHMatching role (n + 1) (scheduledPairMatching role n m word (e⁻¹) (f⁻¹)) :=
  scheduledFullFinalPerm_matching role n m word e f

theorem scheduledFinalRelativePerm_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word}) (e f : FinalParityReassignments n m)
    (i : CopyScheduleAtoms role (n + 1)) :
    copyScheduleOrigin (n + 1) (scheduledFinalRelativePerm role n m word e f i).val =
      copyScheduleOrigin (n + 1) i.val := by
  have hi := scheduledFullFinalPerm_origin role n m word e
    ((scheduledFullFinalPerm role n m word e).symm (scheduledFullFinalPerm role n m word f i))
  rw [Equiv.apply_symm_apply] at hi
  exact hi.symm.trans (scheduledFullFinalPerm_origin role n m word f i)

/-- The witness is the actual shorter anchor and a moved bulk prime slot. -/
theorem scheduled_final_relative_interaction {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (anchor : Fin (n + 1) → I) (ha : ∀ j, role (anchor j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ (h : CopyScheduleH role (n + 1)) (j : Fin (n + 1)) (sign : Bool),
      let a := scheduledRetainedEmbedding role (n + 1)
        (.inr (scheduledPastAnchor role n (anchor j) j (ha j) sign))
      let b := scheduledRetainedEmbedding role (n + 1) (.inl h)
      let G := graphDifference (scheduledSurvivorGraph role pivot (n + 1))
        (transportGraph (scheduledFinalRelativePerm role n m word e f)
          (scheduledSurvivorGraph role pivot (n + 1)))
      a ≠ b ∧ (G a b = 2 ∨ G a b = -2) ∧ G b a = 0 := by
  have hinv : e⁻¹ ≠ f⁻¹ := fun h => hef (inv_injective h)
  obtain ⟨h, j, sign, hfwd, hrev⟩ :=
    scheduled_final_pair_interaction role pivot n m word anchor ha hp (e⁻¹) (f⁻¹) hinv
  refine ⟨h, j, sign, ?_, ?_, ?_⟩
  · exact (scheduledRetainedEmbedding role (n + 1)).injective.ne (by simp)
  · rw [scheduledFinalRelativePerm_matching, scheduledHMatching_graph]
    exact hfwd
  · rw [scheduledFinalRelativePerm_matching, scheduledHMatching_graph]
    exact hrev

theorem scheduled_final_relative_nonprincipal {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (anchor : Fin (n + 1) → I) (ha : ∀ j, role (anchor j) = .anchor j)
    (hp : ∀ k < n + 1, role (pivot k) = .pivot k)
    (χ : CopyScheduleAtoms role (n + 1) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (Q : CopyScheduleAtoms role (n + 1) → Finset ℕ)
    (hsquare : ∀ j sign q, q ∈ Q (scheduledRetainedEmbedding role (n + 1)
      (.inr (scheduledPastAnchor role n (anchor j) j (ha j) sign))) →
      χ (scheduledRetainedEmbedding role (n + 1)
        (.inr (scheduledPastAnchor role n (anchor j) j (ha j) sign))) q ^ 2 ≠ 1)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ a b : CopyScheduleAtoms role (n + 1), a ≠ b ∧
      (∀ q ∈ Q a, χ a q ^ graphDifference (scheduledSurvivorGraph role pivot (n + 1))
        (transportGraph (scheduledFinalRelativePerm role n m word e f)
          (scheduledSurvivorGraph role pivot (n + 1))) a b ≠ 1) ∧
      graphDifference (scheduledSurvivorGraph role pivot (n + 1))
        (transportGraph (scheduledFinalRelativePerm role n m word e f)
          (scheduledSurvivorGraph role pivot (n + 1))) b a = 0 := by
  obtain ⟨h, j, sign, hab, hfwd, hrev⟩ :=
    scheduled_final_relative_interaction role pivot n m word anchor ha hp e f hef
  exact ⟨_, _, hab, (fun q hq => signed_square_nonprincipal _
    (hsquare j sign q hq) _ hfwd), hrev⟩

theorem scheduled_final_pair_reindex {I A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (e f : FinalParityReassignments n m)
    (μ : I → A → ℝ) (F G : (CopyScheduleAtoms role (n + 1) → A) → ℂ) :
    (∑ q, (scheduledPrimePrior role (n + 1) μ q : ℂ) *
      (F (scheduledFullSamplePerm role n m word e q) *
        conj (G (scheduledFullSamplePerm role n m word f q)))) =
    ∑ q, (scheduledPrimePrior role (n + 1) μ q : ℂ) *
      (F q * conj (G (fun i => q (scheduledFinalRelativePerm role n m word e f i)))) := by
  have h := scheduledFullSamplePerm_mean role n m word e μ
    (fun q => F q * conj (G (fun i => q (scheduledFinalRelativePerm role n m word e f i))))
  apply Eq.trans ?_ h
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  congr 1
  apply congrArg conj
  apply congrArg G
  funext i
  change q (scheduledFullFinalPerm role n m word f i) =
    q (scheduledFullFinalPerm role n m word e
      ((scheduledFullFinalPerm role n m word e).symm (scheduledFullFinalPerm role n m word f i)))
  rw [Equiv.apply_symm_apply]

end Ostmann

end OAI
