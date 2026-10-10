import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.EnumeratedBest

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {I Y : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]

lemma average_dep_pi_apply (i : I) (X : Ω i → ℝ) :
    average (fun s : ∀ j, Ω j => X (s i)) = average X := by
  classical
  rw [average_equiv (Equiv.piSplitAt i Ω)
    (fun s : ∀ j, Ω j => X (s i)) (fun p => X p.1) (fun _ => rfl),average_prod]
  simp

lemma probability_dep_pi_apply (i : I) (P : Ω i → Prop) :
    probability (fun s : ∀ j, Ω j => P (s i)) = probability P := by
  classical
  exact average_dep_pi_apply i (fun s => if P s then 1 else 0)

variable [DecidableEq Y]

noncomputable def enumerateBranches (cost : Y → ℝ) (fallback : Y)
    (trial : ∀ i, Ω i → Y) (seed : ∀ i, Ω i) : Y :=
  enumeratedBest cost fallback (fun i => trial i (seed i))

omit [DecidableEq I] [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] in
lemma enumerateBranches_feasible (cost : Y → ℝ) (fallback : Y)
    (trial : ∀ i, Ω i → Y) (P : Y → Prop) (hfall : P fallback)
    (htrial : ∀ i s, P (trial i s)) (seed : ∀ i, Ω i) :
    P (enumerateBranches cost fallback trial seed) := by
  unfold enumerateBranches
  rcases enumeratedBest_mem cost fallback (fun i => trial i (seed i)) with h | ⟨i,h⟩
  · rw [h]; exact hfall
  · rw [h]; exact htrial i (seed i)

omit [DecidableEq I] [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] in
lemma enumerateBranches_le (cost : Y → ℝ) (fallback : Y)
    (trial : ∀ i, Ω i → Y) (seed : ∀ i, Ω i) :
    cost (enumerateBranches cost fallback trial seed) ≤ cost fallback ∧
    ∀ i, cost (enumerateBranches cost fallback trial seed) ≤ cost (trial i (seed i)) :=
  enumeratedBest_le cost fallback _

lemma enumerateBranches_success (cost : Y → ℝ) (fallback : Y)
    (trial : ∀ i, Ω i → Y) (i : I) (B p : ℝ)
    (hsuccess : p ≤ probability (fun s : Ω i => cost (trial i s) ≤ B)) :
    p ≤ probability (fun seed : ∀ i, Ω i => cost (enumerateBranches cost fallback trial seed) ≤ B) := by
  rw [← probability_dep_pi_apply i] at hsuccess
  apply hsuccess.trans
  exact probability_mono (fun seed hs => ((enumerateBranches_le cost fallback trial seed).2 i).trans hs)

end MetricKMedianRecovery.FiniteSampling

end OAI
