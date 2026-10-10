import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerKeyLocalityLemmas

namespace OAI

section

namespace PerfectCompleteness.LowerCutScalar

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

abbrev Values (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (A : Slots branch n → Type u) :=
  TerminalIndex repeats p → space 𝕜 branch (m + 1) (p.family A)

def reconstruct (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) → (A : Slots branch n → Type u) →
      Values 𝕜 repeats p A → CutTerminalSplit.ExteriorTape 𝕜 repeats p A →
        space 𝕜 branch n A
  | _, _, .refl _, _, values, _ => values ()
  | n + 1, _, .step i p, A, values, exterior =>
      RecursiveSampler.combine 𝕜 A i (repeats (n + 1))
        (fun j => exterior ⟨.inl j, not_isTerminal_ordinary repeats i p j⟩)
        (fun h => reconstruct 𝕜 repeats p (childFamily A i)
          (fun terminal => values ((h, false), terminal))
          (CutSamplerReplayGrouping.subExterior 𝕜 repeats i p A (h, false) exterior))
        (fun h => reconstruct 𝕜 repeats p (childFamily A i)
          (fun terminal => values ((h, true), terminal))
          (CutSamplerReplayGrouping.subExterior 𝕜 repeats i p A (h, true) exterior))

@[simp] theorem reconstruct_refl (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (A : Slots branch (m + 1) → Type u)
    (values : Values 𝕜 repeats (.refl (m + 1)) A)
    (exterior : CutTerminalSplit.ExteriorTape 𝕜 repeats (.refl (m + 1)) A) :
    reconstruct 𝕜 repeats (.refl (m + 1)) A values exterior = values () := rfl

theorem reconstruct_step (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n (m + 1))
    (A : Slots branch (n + 1) → Type u)
    (values : Values 𝕜 repeats (.step i p) A)
    (exterior : CutTerminalSplit.ExteriorTape 𝕜 repeats (.step i p) A) :
    reconstruct 𝕜 repeats (.step i p) A values exterior =
      RecursiveSampler.combine 𝕜 A i (repeats (n + 1))
        (fun j => exterior ⟨.inl j, not_isTerminal_ordinary repeats i p j⟩)
        (fun h => reconstruct 𝕜 repeats p (childFamily A i)
          (fun terminal => values ((h, false), terminal))
          (CutSamplerReplayGrouping.subExterior 𝕜 repeats i p A (h, false) exterior))
        (fun h => reconstruct 𝕜 repeats p (childFamily A i)
          (fun terminal => values ((h, true), terminal))
          (CutSamplerReplayGrouping.subExterior 𝕜 repeats i p A (h, true) exterior)) := rfl

theorem reconstruct_splitTape (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (A : Slots branch n → Type u)
      (tape : CutSamplerRefinement.Tape 𝕜 repeats p A),
      reconstruct 𝕜 repeats p A
          (fun terminal => UniformChildSum.recursiveSum (p.family A)
            ((CutTerminalSplit.splitTape 𝕜 repeats p A tape).1 terminal))
          (CutTerminalSplit.splitTape 𝕜 repeats p A tape).2 =
        CutSamplerRefinement.evaluate 𝕜 repeats p A tape := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro A tape
          rfl
      | step i p =>
          intro A tape
          rw [reconstruct_step, CutSamplerLocality.evaluate_step]
          apply congrArg₂ (RecursiveSampler.combine 𝕜 A i (repeats (n + 1))
            (fun j => tape (.inl j)))
          · funext h
            rw [CutSamplerReplayGrouping.subExterior_splitTape]
            simp_rw [CutTerminalZero.splitTape_terminal_step]
            exact ih p (childFamily A i)
              (CutSamplerLocality.subTape 𝕜 repeats i p A tape h false)
          · funext h
            rw [CutSamplerReplayGrouping.subExterior_splitTape]
            simp_rw [CutTerminalZero.splitTape_terminal_step]
            exact ih p (childFamily A i)
              (CutSamplerLocality.subTape 𝕜 repeats i p A tape h true)

theorem reconstruct_join (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (A : Slots branch n → Type u)
    (terminal : CutTerminalSplit.TerminalTape 𝕜 repeats p A)
    (exterior : CutTerminalSplit.ExteriorTape 𝕜 repeats p A) :
    reconstruct 𝕜 repeats p A
        (fun call => UniformChildSum.recursiveSum (p.family A) (terminal call)) exterior =
      CutSamplerRefinement.evaluate 𝕜 repeats p A
        ((CutTerminalSplit.splitTape 𝕜 repeats p A).symm (terminal, exterior)) := by
  simpa only [Equiv.apply_symm_apply] using
    reconstruct_splitTape 𝕜 repeats p A
      ((CutTerminalSplit.splitTape 𝕜 repeats p A).symm (terminal, exterior))

end
end PerfectCompleteness.LowerCutScalar

end

end OAI
