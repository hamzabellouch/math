import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Basic

namespace OAI

/-! The compactness extraction used for uniform shooting-parameter estimates. -/

open Filter
namespace DefocusingNLS

theorem radial_compact_bad_subsequence {K : Type*} [MetricSpace K] [CompactSpace K]
    (P : ℕ → K → Prop) (h : ¬ ∀ᶠ n in atTop, ∀ x, P n x) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ x : ℕ → K, ∃ x₀ : K,
      Tendsto x atTop (nhds x₀) ∧ ∀ i, ¬ P (s i) (x i) := by
  classical
  have hbad : ∃ᶠ n in atTop, ¬ ∀ x, P n x := by
    simpa only [Filter.Frequently,not_not] using h
  have hf : ∀ N : ℕ, ∃ n, N ≤ n ∧ ∃ x, ¬ P n x := by
    intro N
    obtain ⟨n,hn,hbadn⟩ := hbad.forall_exists_of_atTop N
    exact ⟨n,hn,not_forall.mp hbadn⟩
  choose f hfle x hfail using hf
  let s : ℕ → ℕ := Nat.rec (f 0) (fun _ a => f (a+1))
  have hs : StrictMono s := strictMono_nat_of_lt_succ (fun i => by
    change s i < f (s i+1)
    exact (Nat.lt_succ_self _).trans_le (hfle _))
  have hbad' : ∀ i, ∃ y, ¬ P (s i) y := by
    intro i
    cases i with
    | zero => exact ⟨x 0,hfail 0⟩
    | succ i => exact ⟨x (s i+1),hfail (s i+1)⟩
  choose y hy using hbad'
  obtain ⟨y₀,σ,hσ,hylim⟩ := CompactSpace.tendsto_subseq y
  exact ⟨s ∘ σ,hs.comp hσ,y ∘ σ,y₀,hylim,fun i => hy (σ i)⟩

end DefocusingNLS

end OAI
