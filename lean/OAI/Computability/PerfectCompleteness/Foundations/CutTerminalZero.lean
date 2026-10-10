import OAI.Computability.PerfectCompleteness.Foundations.CutTerminalSplit
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerLocality

namespace OAI

section

namespace PerfectCompleteness.CutTerminalZero

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls
open scoped Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}
  (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)

theorem terminalFactorEquiv_refl (A : Slots branch (m + 1) → Type u)
    (terminal : TerminalIndex repeats (.refl (m + 1)))
    (x : CutSamplerRefinement.RefinedSpace 𝕜 repeats (.refl (m + 1)) A
      (drawIndex repeats (.refl (m + 1)) terminal)) :
    CutTerminalSplit.terminalFactorEquiv 𝕜 repeats (.refl (m + 1)) A terminal x = x := rfl

theorem terminalFactorEquiv_step (i : Fin (branch n))
    (p : Path branch n (m + 1)) (A : Slots branch (n + 1) → Type u)
    (call : Fin (repeats (n + 1)) × Bool) (terminal : TerminalIndex repeats p)
    (x : CutSamplerRefinement.RefinedSpace 𝕜 repeats p (childFamily A i)
      (drawIndex repeats p terminal)) :
    CutTerminalSplit.terminalFactorEquiv 𝕜 repeats (.step i p) A (call, terminal) x =
      CutTerminalSplit.terminalFactorEquiv 𝕜 repeats p (childFamily A i) terminal x := rfl

theorem splitTape_terminal_step (i : Fin (branch n))
    (p : Path branch n (m + 1)) (A : Slots branch (n + 1) → Type u)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats (.step i p) A)
    (h : Fin (repeats (n + 1))) (b : Bool) (terminal : TerminalIndex repeats p) :
    (CutTerminalSplit.splitTape 𝕜 repeats (.step i p) A tape).1 ((h, b), terminal) =
      (CutTerminalSplit.splitTape 𝕜 repeats p (childFamily A i)
        (CutSamplerLocality.subTape 𝕜 repeats i p A tape h b)).1 terminal := by
  simp only [CutTerminalSplit.splitTape_terminal_apply]
  rfl

theorem zeroAtClean_iff (p : Path branch n (m + 1)) :
    ∀ (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
      (tape : CutSamplerRefinement.Tape 𝕜 repeats p A),
      (∀ terminal i, clean i →
        (CutTerminalSplit.splitTape 𝕜 repeats p A tape).1 terminal i = 0) ↔
      CutSamplerLocality.ZeroAtClean 𝕜 repeats p A clean tape := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro A clean tape
          constructor
          · intro hzero i hi
            exact hzero () i hi
          · intro hzero terminal i hi
            cases terminal
            exact hzero i hi
      | step i p =>
          intro A clean tape
          constructor
          · intro hzero h b
            apply (ih p (childFamily A i) clean
              (CutSamplerLocality.subTape 𝕜 repeats i p A tape h b)).mp
            intro terminal j hj
            apply Subtype.ext
            have hread := congrArg
              (fun f : CutTerminalSplit.TerminalFactor 𝕜 (.step i p) A => (f j).val)
              (splitTape_terminal_step 𝕜 repeats i p A tape h b terminal)
            exact hread.symm.trans (congrArg Subtype.val (hzero ((h, b), terminal) j hj))
          · intro hzero terminal j hj
            rcases terminal with ⟨⟨h, b⟩, terminal⟩
            have hsub := (ih p (childFamily A i) clean
              (CutSamplerLocality.subTape 𝕜 repeats i p A tape h b)).mpr (hzero h b)
            apply Subtype.ext
            have hread := congrArg
              (fun f : CutTerminalSplit.TerminalFactor 𝕜 (.step i p) A => (f j).val)
              (splitTape_terminal_step 𝕜 repeats i p A tape h b terminal)
            exact hread.trans (congrArg Subtype.val (hsub terminal j hj))

theorem evaluate_factors_of_split_zero (p : Path branch n (m + 1))
    (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats p A)
    (hzero : ∀ terminal i, clean i →
      (CutTerminalSplit.splitTape 𝕜 repeats p A tape).1 terminal i = 0) :
    (CutSamplerRefinement.evaluate 𝕜 repeats p A tape).val ∈
      FactoredFunctions.factoringSpace (CutSamplerLocality.view p A clean) :=
  CutSamplerLocality.evaluate_factors 𝕜 repeats p A clean tape
    ((zeroAtClean_iff 𝕜 repeats p A clean tape).mp hzero)

end
end PerfectCompleteness.CutTerminalZero

end

end OAI
