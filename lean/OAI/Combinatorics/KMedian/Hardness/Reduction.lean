import Mathlib
import OAI.Combinatorics.KMedian.Hardness.Classes
import OAI.Combinatorics.KMedian.Hardness.Threads
import OAI.Combinatorics.KMedian.Hardness.Verdict

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Complexity

def HasSeparator (δ : ℝ) : Prop :=
  ∃ d : Input → Bool, FinitePolyTime Input.encode encodeBit d ∧
    (∀ C, C.Perfect → d C = true) ∧
    (∀ C, C.Sound δ → d C = false)

theorem approximation_gives_separator {α : ℝ}
    (hα : α ∈ approximationFactors) (hsmall : α < 1+2/Real.exp 1) :
    ∃ δ : ℝ, 0 < δ ∧ HasSeparator δ := by
  obtain ⟨δ,hδ,q,hq₁,hq₂⟩ := exists_coverage_margin hsmall
  obtain ⟨algorithm,halg,hcorrect⟩ := hα
  let result : Input → List Bool := algorithm ∘ Input.toMedian
  have hr : FinitePolyTime Input.encode id result :=
    Input.reduction_finite_poly.comp halg
  have hv : FinitePolyTime (Binary.encodePair id Input.encode) encodeBit
      (fun x : List Bool × Input => x.2.accepts q x.1) :=
    ⟨(Input.verdictProgram q).stock,(Input.verdictProgram q).finite_work⟩
  refine ⟨δ,hδ,(fun C => C.accepts q (result C)), ?_, ?_, ?_⟩
  · exact hr.withInput.comp hv
  · intro C hC
    exact C.accepts_of_perfect hq₁ hC (hcorrect C.toMedian)
  · intro C hC
    exact C.rejects_of_sound hq₂.le hC (hcorrect C.toMedian)

theorem separator_decides_reduction {δ : ℝ} (hsep : HasSeparator δ)
    {L : Language} {r : Word → Input}
    (hr : FinitePolyTime id Input.encode r)
    (hyes : ∀ x, x ∈ L → (r x).Perfect)
    (hno : ∀ x, x ∉ L → (r x).Sound δ) : L ∈ P := by
  obtain ⟨d,hd,hy,hn⟩ := hsep
  refine ⟨d ∘ r,hr.comp hd,?_⟩
  intro x
  constructor
  · intro hx
    by_contra h
    have hh := hn (r x) (hno x h)
    exact Bool.noConfusion (hx.symm.trans hh)
  · intro hx
    exact hy (r x) (hyes x hx)

theorem remaining_gap_obstruction (hPNP : PNeNP) {α : ℝ}
    (hα : α ∈ approximationFactors) (hsmall : α < 1+2/Real.exp 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : Language, L ∈ NP ∧
      ¬ ∃ r : Word → Input, FinitePolyTime id Input.encode r ∧
        (∀ x, x ∈ L → (r x).Perfect) ∧
        (∀ x, x ∉ L → (r x).Sound δ) := by
  obtain ⟨δ,hδ,hsep⟩ := approximation_gives_separator hα hsmall
  obtain ⟨L,hL,hnot⟩ := exists_NP_not_P hPNP
  refine ⟨δ,hδ,L,hL,?_⟩
  rintro ⟨r,hr,hy,hn⟩
  exact hnot (separator_decides_reduction hsep hr hy hn)

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
