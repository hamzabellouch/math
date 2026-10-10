import Mathlib

namespace OAI

noncomputable section

open Set
open scoped SetRel Uniformity ENNReal

namespace Problem340

theorem exists_open_neighborhood_dynCover {X : Type*} [TopologicalSpace X]
    {T : X → X} (hT : Continuous T) {K : Set X} {U : SetRel X X}
    (hU : IsOpen U) {m : ℕ} {s : Finset X}
    (hs : Dynamics.IsDynCoverOf T K U m s) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ Dynamics.IsDynCoverOf T V U m s := by
  let V : Set X := ⋃ y ∈ (s : Set X), {x | (x, y) ∈ Dynamics.dynEntourage T U m}
  refine ⟨V, ?_, ?_, ?_⟩
  · apply isOpen_biUnion
    intro y _hy
    exact (isOpen.dynEntourage hT hU m).preimage (continuous_id.prodMk continuous_const)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hs hx
    exact Set.mem_iUnion₂.mpr ⟨y, hy, hxy⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨y, hy, hxy⟩

theorem eventually_exists_small_dynCover {X : Type*} [UniformSpace X]
    {T : X → X} {K : Set X} (hK : IsCompact K) (hInv : MapsTo T K K)
    (hzero : Dynamics.coverEntropy T K = 0) {U : SetRel X X} (hU : U ∈ 𝓤 X)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∃ s : Finset X,
      Dynamics.IsDynCoverOf T K U n s ∧
      ENNReal.log (s.card : ℝ≥0∞) ≤ (ε : EReal) * n := by
  have hr : Dynamics.coverEntropyEntourage T K U < (ε : EReal) := by
    have hle := Dynamics.coverEntropyEntourage_le_coverEntropy T K hU
    rw [hzero] at hle
    exact hle.trans_lt (by exact_mod_cast hε)
  have he := ExpGrowth.eventually_le_exp hr
  filter_upwards [he] with n hn
  obtain ⟨s, hs, hcard⟩ := (Dynamics.coverMincard_finite_iff T K U n).mp
    (Dynamics.coverMincard_finite_of_isCompact_invariant hK hInv hU n)
  refine ⟨s, hs, ?_⟩
  have hlog := ENNReal.log_monotone hn
  rw [EReal.log_exp] at hlog
  have heq : (s.card : ℝ≥0∞) = (Dynamics.coverMincard T K U n).toENNReal := by
    exact_mod_cast hcard
  rw [heq]
  exact hlog

end Problem340

end

end OAI
