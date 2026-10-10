import OAI.Analysis.CircleDomains.Topology.CountablePathConcatenation
import OAI.Analysis.CircleDomains.Modulus.PathVariation

namespace OAI

/-! Exact arclength addition over the decreasing collar intervals. This is
 an extended-real identity and therefore does not assume rectifiability. -/

open Set Function Filter
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem collar_variation_partial (γ : PathTime → X) (N : ℕ) :
    (∑ n ∈ Finset.range N, eVariationOn γ (collarCell n)) =
      eVariationOn γ (Icc (collarTime N) ⊤) := by
  induction N with
  | zero => simp [collarTime_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, add_comm]
    have he := eVariationOn.Icc_add_Icc γ (s := univ)
      (collarTime_strictAnti (Nat.lt_succ_self N)).le (le_top : collarTime N ≤ ⊤)
      (mem_univ (collarTime N))
    simpa only [univ_inter, collarCell] using he

theorem collar_variation_sum (γ : C(PathTime, X)) :
    eVariationOn γ univ = ∑' n, eVariationOn γ (collarCell n) := by
  apply le_antisymm
  · have he := eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt
      (γ.continuous.continuousAt (x := (⊥ : PathTime))).continuousWithinAt
      (b := (⊤ : PathTime))
    rw [Icc_bot_top] at he
    rw [← he, eVariationOn]
    apply iSup_le
    rintro ⟨k, u, hu, hmem⟩
    obtain ⟨N, hN⟩ := (collarTime_tendsto.eventually (gt_mem_nhds (hmem 0).1)).exists
    have hall : ∀ i, u i ∈ Icc (collarTime N) ⊤ := by
      intro i
      exact ⟨hN.le.trans (hu (Nat.zero_le i)), le_top⟩
    exact (eVariationOn.sum_le hu hall).trans
      ((collar_variation_partial γ N).symm.le.trans (ENNReal.sum_le_tsum _))
  · rw [ENNReal.tsum_eq_iSup_nat]
    apply iSup_le
    intro N
    rw [collar_variation_partial]
    exact eVariationOn.mono γ (subset_univ _)

theorem collarConcatenation_variation (p : X) (γ : ℕ → C(PathTime, X)) hjoin htail :
    eVariationOn (collarConcatenation p γ hjoin htail) univ =
      ∑' n, eVariationOn (γ n) univ := by
  rw [collar_variation_sum]
  apply tsum_congr
  intro n
  let f := affinePathTime (collarTime (n + 1)) (collarTime n)
  have hf := affinePathTime_strictMono (collarTime_strictAnti (Nat.lt_succ_self n))
  have he := eVariationOn.comp_eq_of_monotoneOn
    (collarConcatenation p γ hjoin htail) f (hf.monotone.monotoneOn univ)
  rw [image_univ, range_affinePathTime (collarTime_strictAnti (Nat.lt_succ_self n))] at he
  change eVariationOn _ (Icc (collarTime (n + 1)) (collarTime n)) = _
  rw [← he]
  apply eVariationOn.congr
  intro t _
  exact collarConcatenation_affine p γ hjoin htail n t

theorem collarConcatenation_rectifiable (p : X) (γ : ℕ → C(PathTime, X)) hjoin htail
    (hfinite : (∑' n, eVariationOn (γ n) univ) < ∞) :
    BoundedVariationOn (collarConcatenation p γ hjoin htail) univ := by
  change eVariationOn _ _ ≠ ∞
  rw [collarConcatenation_variation]
  exact hfinite.ne

end CircleDomainRigidity

end

end OAI
