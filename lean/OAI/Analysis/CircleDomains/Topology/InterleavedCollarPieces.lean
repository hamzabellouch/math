import OAI.Analysis.CircleDomains.Modulus.CollarConcatenationCost

namespace OAI

/-! Interleaving actual retained fragments with their joining arcs preserves
the endpoint matches and adds exactly the two series of costs. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

def interleavePieces {α : Type*} (a b : ℕ → α) (n : ℕ) : α :=
  if n % 2 = 0 then a (n / 2) else b (n / 2)

@[simp] theorem interleavePieces_even {α : Type*} (a b : ℕ → α) (n : ℕ) :
    interleavePieces a b (2*n) = a n := by simp [interleavePieces]

@[simp] theorem interleavePieces_odd {α : Type*} (a b : ℕ → α) (n : ℕ) :
    interleavePieces a b (2*n+1) = b n := by simp [interleavePieces, Nat.add_div]

theorem interleavePieces_join {X : Type*}
    (a b : ℕ → PathTime → X)
    (hleft : ∀n, b n ⊥ = a (n+1) ⊤) (hright : ∀n, b n ⊤ = a n ⊥) :
    ∀n, interleavePieces a b (n+1) ⊤ = interleavePieces a b n ⊥ := by
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hn : n = 2 * (n/2) := by omega
    rw [hn]
    simpa only [interleavePieces_odd, interleavePieces_even] using hright (n/2)
  · have hn : n = 2 * (n/2)+1 := by omega
    rw [hn]
    have he : 2*(n/2)+1+1 = 2*(n/2+1) := by omega
    rw [he]
    simpa only [interleavePieces_even, interleavePieces_odd] using (hleft (n/2)).symm

theorem interleavePieces_tail {X : Type*} [TopologicalSpace X]
    (a b : ℕ → PathTime → X) (p : X)
    (ha : ∀V ∈ 𝓝 p, ∃N : ℕ, ∀n ≥ N, ∀t, a n t ∈ V)
    (hb : ∀V ∈ 𝓝 p, ∃N : ℕ, ∀n ≥ N, ∀t, b n t ∈ V) :
    ∀V ∈ 𝓝 p, ∃N : ℕ, ∀n ≥ N, ∀t, interleavePieces a b n t ∈ V := by
  intro V hV
  obtain ⟨N, hN⟩ := ha V hV
  obtain ⟨M, hM⟩ := hb V hV
  refine ⟨2 * max N M, ?_⟩
  intro n hn t
  have hNn : N ≤ n/2 := by omega
  have hMn : M ≤ n/2 := by omega
  unfold interleavePieces
  split
  · exact hN _ hNn t
  · exact hM _ hMn t

theorem tsum_interleavePieces (a b : ℕ → ℝ≥0∞) :
    (∑' n, interleavePieces a b n) = (∑' n, a n) + ∑' n, b n := by
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
  simp only [interleavePieces_even, interleavePieces_odd]

theorem tsum_cost_interleavePieces {α : Type*} (a b : ℕ → α) (c : α → ℝ≥0∞) :
    (∑' n, c (interleavePieces a b n)) = (∑'n, c (a n)) + ∑'n, c (b n) := by
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
  simp only [interleavePieces_even, interleavePieces_odd]

end CircleDomainRigidity

end

end OAI
