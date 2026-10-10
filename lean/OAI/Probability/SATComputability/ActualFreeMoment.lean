import OAI.Probability.SATComputability.ActiveProcess

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

local instance actualFreeMomentCandidateMeasurable (n : ℕ) :
    MeasurableSpace (DeletionCandidate n) := ⊤
local instance actualFreeMomentCandidateSingleton (n : ℕ) :
    MeasurableSingletonClass (DeletionCandidate n) := ⟨fun _ => trivial⟩

noncomputable def freeGap (n M r : ℕ) (xs : Fin M → Finset (DeletionCandidate (n+1))) : ℝ :=
  (maskLifetime M (freeDeletionBudgetMask (n+1) r 0) xs -
    maskLifetime M (deletionBudgetMask (n+1) r) xs)^(6/5 : ℝ)

noncomputable def restoredGap (n M r : ℕ)
    (base f t : Fin M → Finset (DeletionCandidate n)) : ℝ :=
  (maskLifetime M (deletionBudgetMask n r) base -
    maskLifetime M (deletionBudgetMask (n+1) r)
      (fun j => restoredMask (base j) (f j) (t j)))^(6/5 : ℝ)

theorem actual_free_deletion_moment_zero {n : ℕ} [NeZero n] (r : ℕ) :
    (FiniteLaw.pi (fun _ : Fin (20*(n+1)) =>
      candidateBlock (n := n+1) 1 3 Finset.univ)).expect (freeGap n (20*(n+1)) r) ≤
      deletionMomentConstant := by
  let M := 20*(n+1)
  let rate := clauseAtomRate n
  let ψ := restoredGap n M r
  let B := gridMaskLaw M rate (baseMask (n := n))
  let P := gridMaskLaw M rate (incidentMask (n := n))
  have hgrid := gridMaskLaw_clauses (n := n+1) M 3 rate
  change gridMaskLaw M rate clauseMask = _ at hgrid
  have hn := clause_atom_normalization n
  change rate * Fintype.card (Fin 3 → SignedLiteral (n+1)) = 1 at hn
  rw [hn] at hgrid
  have hm : clauseMask (n := n+1) (k := 3) =
      (fun a => clauseMask (classClause a)) ∘ clauseClassesEquiv n := by
    funext a
    simp only [Function.comp_apply, classClause, Equiv.symm_apply_apply]
  have hleft : Integrable (fun c : ActiveClause n × Fin M → ℕ =>
      freeGap n M r (maskGrid activeMask c)) (poissonCountLaw (ActiveClause n × Fin M) rate) :=
    bounded_finite_observable _ (maskGrid activeMask) (measurable_of_countable _) (freeGap n M r)
  have hright : Integrable (fun c : ActiveClause n × Fin M → ℕ =>
      ψ (maskGrid baseMask (fun p => c (.inl p.1,p.2)))
        (maskGrid incidentMask (fun p => c (.inr (true,p.1),p.2)))
        (maskGrid incidentMask (fun p => c (.inr (false,p.1),p.2))))
      (poissonCountLaw (ActiveClause n × Fin M) rate) := by
    exact bounded_finite_observable _
      (fun c : ActiveClause n × Fin M → ℕ =>
        (maskGrid baseMask (fun p => c (.inl p.1,p.2)),
          maskGrid incidentMask (fun p => c (.inr (true,p.1),p.2)),
          maskGrid incidentMask (fun p => c (.inr (false,p.1),p.2))))
      (measurable_of_countable _) (fun p => ψ p.1 p.2.1 p.2.2)
  calc
    _ = (gridMaskLaw M rate clauseMask).expect (freeGap n M r) := by rw [hgrid]
    _ = (gridMaskLaw M rate (fun a => clauseMask (classClause a))).expect (freeGap n M r) := by
      exact congrArg (fun P => P.expect (freeGap n M r))
        ((congrArg (gridMaskLaw M rate) hm).trans
          (gridMaskLaw_equiv (clauseClassesEquiv n) rate (fun a => clauseMask (classClause a))))
    _ = ∫ c : ActiveClause n × Fin M → ℕ, freeGap n M r (maskGrid activeMask c)
        ∂poissonCountLaw (ActiveClause n × Fin M) rate := by
      rw [gridMaskLaw_expect, active_original_expect]
    _ ≤ ∫ c : ActiveClause n × Fin M → ℕ,
        ψ (maskGrid baseMask (fun p => c (.inl p.1,p.2)))
          (maskGrid incidentMask (fun p => c (.inr (true,p.1),p.2)))
          (maskGrid incidentMask (fun p => c (.inr (false,p.1),p.2)))
          ∂poissonCountLaw (ActiveClause n × Fin M) rate :=
      integral_mono hleft hright (fun c => active_gap_domination c)
    _ = B.expect (fun base => P.expect (fun f => P.expect (fun t => ψ base f t))) :=
      active_streams_expect rate ψ
    _ = P.expect (fun f => P.expect (fun t => B.expect (fun base => ψ base f t))) := by
      rw [finite_expect_comm B P]
      apply P.expect_congr
      intro f
      exact finite_expect_comm B P _
    _ ≤ deletionMomentConstant := by
      dsimp only [B]
      rw [base_grid_law]
      exact incident_restored_uniform_moment r

end FixedClauseThreshold.Computability

end OAI
