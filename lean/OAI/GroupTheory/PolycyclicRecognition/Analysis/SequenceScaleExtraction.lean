import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteModeProfileChains

namespace OAI

/-! # Cofinal, strictly increasing scales with one fixed finite mode -/

noncomputable section
namespace PolycyclicRecognition

open Filter

/-- A divergent real scale can be made strictly increasing and at least one
by restricting the original sequence. -/
theorem exists_strictMono_scale_subsequence (scale : ℕ → ℝ)
    (hs : Tendsto scale atTop atTop) :
    ∃ u : ℕ → ℕ, StrictMono u ∧ StrictMono (scale ∘ u) ∧
      ∀ n, 1 ≤ scale (u n) := by
  classical
  obtain ⟨n₀, hn₀⟩ := (hs.eventually (eventually_ge_atTop (1 : ℝ))).exists
  have he (n : ℕ) : ∃ k : ℕ, n < k ∧ scale n < scale k :=
    ((eventually_gt_atTop n).and (hs.eventually (eventually_gt_atTop (scale n)))).exists
  choose next hnext hscale using he
  let u : ℕ → ℕ := Nat.rec n₀ (fun _ k => next k)
  have hu : StrictMono u := strictMono_nat_of_lt_succ fun n => hnext (u n)
  have hv : StrictMono (scale ∘ u) :=
    strictMono_nat_of_lt_succ fun n => hscale (u n)
  refine ⟨u, hu, hv, fun n => hn₀.trans ?_⟩
  exact hv.monotone (Nat.zero_le n)

/-- Fix a finite mode first, then make the real scales strictly increasing.
This applies in particular to the finite family of word-basis selections. -/
theorem exists_constant_mode_strict_scale {I : Type*} [Finite I]
    (mode : ℕ → I) (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop) :
    ∃ (i : I) (u : ℕ → ℕ), StrictMono u ∧ StrictMono (scale ∘ u) ∧
      (∀ n, 1 ≤ scale (u n)) ∧ ∀ n, mode (u n) = i := by
  obtain ⟨i, v, hv, hi⟩ := exists_constant_mode_subsequence mode
  obtain ⟨u, hu, hsu, hs1⟩ := exists_strictMono_scale_subsequence
    (scale ∘ v) (hs.comp hv.tendsto_atTop)
  exact ⟨i, v ∘ u, hv.comp hu, hsu, hs1, fun n => hi (u n)⟩

end PolycyclicRecognition

end

end OAI
