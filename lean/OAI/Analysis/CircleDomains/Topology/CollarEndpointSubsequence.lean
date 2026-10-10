import OAI.Analysis.CircleDomains.Topology.CollarFragmentSelection

namespace OAI

/-! Convergent endpoints may be placed in the successive chosen collars
without losing a cofinal, strictly increasing original-path subsequence. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_subsequence_in_nested_endpoint_neighborhoods
    {X : Type*} [TopologicalSpace X] (x y : ℕ → X) {p q : X}
    (hx : Tendsto x atTop (𝓝 p)) (hy : Tendsto y atTop (𝓝 q))
    (V W : ℕ → Set X) (hV : ∀j, V j ∈ 𝓝 p) (hW : ∀j, W j ∈ 𝓝 q) :
    ∃s : ℕ → ℕ, StrictMono s ∧ ∀n, x (s n) ∈ V (n+1) ∧ y (s n) ∈ W (n+1) := by
  have hchoose : ∀n N : ℕ, ∃k, N < k ∧ x k ∈ V (n+1) ∧ y k ∈ W (n+1) := by
    intro n N
    exact ((eventually_gt_atTop N).and
      ((hx.eventually (hV (n+1))).and (hy.eventually (hW (n+1))))).exists
  choose f hf using hchoose
  let s : ℕ → ℕ := Nat.rec (f 0 0) (fun n k => f (n+1) k)
  have hsucc (n : ℕ) : s (n+1) = f (n+1) (s n) := rfl
  refine ⟨s, strictMono_nat_of_lt_succ (fun n => ?_), ?_⟩
  · rw [hsucc]
    exact (hf (n+1) (s n)).1
  · intro n
    cases n with
    | zero => exact (hf 0 0).2
    | succ n => exact (hf (n+1) (s n)).2

end CircleDomainRigidity

end

end OAI
