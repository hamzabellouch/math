import OAI.Analysis.KadisonKastler.ProjectionNormDecomposition
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

/-! # The strong limit of decreasing Hilbert projections

The squared norms decrease. Their Cauchy estimate identifies the strong
limit with projection onto the intersection, as needed for central vectors.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Decreasing closed subspaces have strongly convergent projections. -/
theorem decreasing_projection_limit (K : ℕ → Submodule ℂ H)
    [∀ n, CompleteSpace (K n)] (hK : Antitone K) (ξ : H) :
    ∃ η : H, (∀ n, η ∈ K n) ∧
      Tendsto (fun n => (K n).starProjection ξ) atTop (𝓝 η) ∧
      ∀ w : H, (∀ n, w ∈ K n) → inner ℂ (ξ - η) w = 0 := by
  let P (n : ℕ) : H →L[ℂ] H := (K n).starProjection
  have hP (n : ℕ) : IsStarProjection (P n) :=
    ⟨Submodule.isIdempotentElem_starProjection _, isSelfAdjoint_starProjection _⟩
  have hnest {m n : ℕ} (hmn : m ≤ n) : P n * P m = P n :=
    Submodule.starProjection_comp_starProjection_of_le (hK hmn)
  let f (n : ℕ) : ℝ := ‖P n ξ‖ ^ 2
  have hid {m n : ℕ} (hmn : m ≤ n) :
      f n + ‖P m ξ - P n ξ‖ ^ 2 = f m := by
    simpa only [sub_apply] using nested_projection_norm_sq_eq (hP n) (hnest hmn) ξ
  have hf : Antitone f := by
    intro m n hmn
    have h := hid hmn
    linarith [sq_nonneg ‖P m ξ - P n ξ‖]
  have ht : Tendsto f atTop (𝓝 (⨅ n, f n)) :=
    tendsto_atTop_ciInf hf ⟨0, by rintro _ ⟨n,rfl⟩; exact sq_nonneg _⟩
  have hc := ht.cauchySeq
  have hpc : CauchySeq (fun n => P n ξ) := by
    rw [Metric.cauchySeq_iff] at hc ⊢
    intro ε hε
    obtain ⟨k,hk⟩ := hc (ε ^ 2) (sq_pos_of_pos hε)
    have hb (m n : ℕ) (hm : k ≤ m) (hn : k ≤ n) (hmn : m ≤ n) :
        dist (P m ξ) (P n ξ) < ε := by
      have hd := hk m hm n hn
      have he := hid hmn
      rw [Real.dist_eq] at hd
      rw [dist_eq_norm]
      nlinarith [le_abs_self (f m - f n), norm_nonneg (P m ξ - P n ξ)]
    refine ⟨k,fun m hm n hn => ?_⟩
    rcases le_total m n with h | h
    · exact hb m n hm hn h
    · simpa only [dist_comm] using hb n m hn hm h
  obtain ⟨η,hη⟩ := cauchySeq_tendsto_of_complete hpc
  refine ⟨η, ?_, hη, ?_⟩
  · intro n
    have hclosed : IsClosed (K n : Set H) :=
      (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace (K n))).isClosed
    apply hclosed.mem_of_tendsto hη
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hK hm (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    have hi : Tendsto (fun n => inner ℂ (ξ - P n ξ) w) atTop
        (𝓝 (inner ℂ (ξ - η) w)) :=
      ((tendsto_const_nhds.sub hη).inner tendsto_const_nhds)
    have hz (n : ℕ) : inner ℂ (ξ - P n ξ) w = 0 :=
      Submodule.starProjection_inner_eq_zero ξ w (hw n)
    exact tendsto_nhds_unique hi (by simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))

end

end KadisonKastler

end OAI
