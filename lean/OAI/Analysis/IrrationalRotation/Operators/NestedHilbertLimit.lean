import Mathlib

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.ProductDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sub_sq_of_nested_inner (u : ℕ → E)
    (hinner : ∀ m n, m ≤ n → inner ℝ (u m) (u n) = ‖u m‖ ^ 2)
    {m n : ℕ} (hmn : m ≤ n) :
    ‖u m - u n‖ ^ 2 = ‖u n‖ ^ 2 - ‖u m‖ ^ 2 := by
  rw [norm_sub_sq_real, hinner m n hmn]
  ring

theorem monotone_norm_sq_of_nested_inner (u : ℕ → E)
    (hinner : ∀ m n, m ≤ n → inner ℝ (u m) (u n) = ‖u m‖ ^ 2) :
    Monotone (fun n => ‖u n‖ ^ 2) := by
  intro m n hmn
  have h := norm_sub_sq_of_nested_inner u hinner hmn
  nlinarith [sq_nonneg ‖u m - u n‖]

theorem norm_sub_sq_eq_abs_of_nested_inner (u : ℕ → E)
    (hinner : ∀ m n, m ≤ n → inner ℝ (u m) (u n) = ‖u m‖ ^ 2)
    (m n : ℕ) :
    ‖u m - u n‖ ^ 2 = |‖u m‖ ^ 2 - ‖u n‖ ^ 2| := by
  rcases le_total m n with hmn | hnm
  · rw [norm_sub_sq_of_nested_inner u hinner hmn,
      abs_of_nonpos (sub_nonpos.mpr (monotone_norm_sq_of_nested_inner u hinner hmn))]
    ring
  · rw [norm_sub_rev, norm_sub_sq_of_nested_inner u hinner hnm,
      abs_of_nonneg (sub_nonneg.mpr (monotone_norm_sq_of_nested_inner u hinner hnm))]

theorem cauchySeq_of_nested_inner (u : ℕ → E)
    (hinner : ∀ m n, m ≤ n → inner ℝ (u m) (u n) = ‖u m‖ ^ 2)
    (hbound : BddAbove (Set.range (fun n => ‖u n‖ ^ 2))) :
    CauchySeq u := by
  have hlim := tendsto_atTop_ciSup (monotone_norm_sq_of_nested_inner u hinner) hbound
  have hc : CauchySeq (fun n => ‖u n‖ ^ 2) := hlim.cauchySeq
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hs := hN m hm n hn
  rw [Real.dist_eq, ← norm_sub_sq_eq_abs_of_nested_inner u hinner m n] at hs
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (u m - u n)]

theorem exists_limit_of_nested_inner [CompleteSpace E] (u : ℕ → E)
    (hinner : ∀ m n, m ≤ n → inner ℝ (u m) (u n) = ‖u m‖ ^ 2)
    (C : ℝ) (hbound : ∀ n, ‖u n‖ ^ 2 ≤ C) :
    ∃ v : E, Tendsto u atTop (𝓝 v) ∧ ‖v‖ ^ 2 ≤ C := by
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_nested_inner u hinner ⟨C, by rintro _ ⟨n, rfl⟩; exact hbound n⟩)
  refine ⟨v, hv, ?_⟩
  exact le_of_tendsto (hv.norm.pow 2) (Eventually.of_forall hbound)

end Invariant233.ProductDensity

end OAI
