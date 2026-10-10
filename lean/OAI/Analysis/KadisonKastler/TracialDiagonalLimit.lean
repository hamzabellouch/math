import OAI.Analysis.KadisonKastler.TracialSequenceQuotient
import OAI.Analysis.KadisonKastler.UltrafilterDiagonal

namespace OAI

/-! # Bounded diagonal limits in the tracial sequence quotient -/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

/-- A uniformly bounded, rapidly two-Cauchy family has a coordinatewise
diagonal representative with the same uniform bound. -/
theorem exists_tracial_diagonal_limit (hω : (ω : Filter ℕ) ≤ atTop)
    (x : ℕ → VaryingBoundedSequence B) (C : ℝ) (hC : 0 ≤ C)
    (hx : ∀ n j, ‖x n j‖ ≤ C) (a : ℕ → ℝ)
    (hfast : ∀ n m, n ≤ m → traceTwoNorm (tracialQuotientTrace τ ω)
      (tracialSequenceQuotientMap τ ω (x m) - tracialSequenceQuotientMap τ ω (x n)) < a n) :
    ∃ y : VaryingBoundedSequence B, ‖y‖ ≤ C ∧ ∀ n,
      traceTwoNorm (tracialQuotientTrace τ ω)
        (tracialSequenceQuotientMap τ ω y - tracialSequenceQuotientMap τ ω (x n)) ≤ a n := by
  classical
  let A : ℕ → Set ℕ := fun m => {j | ∀ n ≤ m, traceTwoNorm (τ j) (x m j - x n j) < a n}
  have hA (m : ℕ) : A m ∈ ω := by
    have he : ∀ᶠ j in (ω : Filter ℕ), ∀ n ∈ Finset.range (m + 1),
        traceTwoNorm (τ j) (x m j - x n j) < a n := by
      apply (eventually_all_finset _).mpr
      intro n hn
      have ht := (tracialQuotientTwoNorm_limit τ ω (x m - x n)).eventually
        (gt_mem_nhds (by simpa only [map_sub] using hfast n m (by simpa using hn)))
      exact ht
    filter_upwards [he] with j hj n hn
    exact hj n (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  obtain ⟨k, hk, hAk⟩ := exists_ultrafilter_diagonal_index ω hω A hA
  let y : VaryingBoundedSequence B := ⟨fun j => x (k j) j,
    memℓp_infty ⟨C, by rintro _ ⟨j, rfl⟩; exact hx (k j) j⟩⟩
  refine ⟨y, lp.norm_le_of_forall_le hC (fun j => hx (k j) j), ?_⟩
  intro n
  have he : ∀ᶠ j in (ω : Filter ℕ), traceTwoNorm (τ j) (y j - x n j) ≤ a n := by
    filter_upwards [hAk, (tendsto_atTop.mp hk) n] with j hj hjn
    exact (hj n hjn).le
  have ht := tracialQuotientTwoNorm_limit τ ω (y - x n)
  rw [map_sub] at ht
  exact le_of_tendsto ht he

end

end KadisonKastler

end OAI
