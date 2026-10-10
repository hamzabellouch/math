import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.OverlapCompatibility

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem exists_lipschitz_open_support {X : Type*} [PseudoMetricSpace X]
    (s : Set X) (hs : IsOpen s) :
    ∃ χ : X → ℝ, LipschitzWith 1 χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ support χ = s := by
  classical
  by_cases hfull : s = univ
  · refine ⟨fun _ => 1, ?_, by simp, ?_⟩
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_self, NNReal.coe_one, one_mul] using! (dist_nonneg (x := x) (y := y))
    · ext x
      simp [Function.support, hfull]
  · have hne : sᶜ.Nonempty := ssubset_univ_iff_nonempty_compl.mp
      (ssubset_iff_subset_ne.mpr ⟨subset_univ s, hfull⟩)
    refine ⟨fun x => min 1 (infDist x sᶜ), (lipschitz_infDist_pt sᶜ).const_min 1, ?_, ?_⟩
    · intro x
      exact ⟨le_min (by norm_num) infDist_nonneg, min_le_left _ _⟩
    · ext x
      change min 1 (infDist x sᶜ) ≠ 0 ↔ x ∈ s
      constructor
      · intro hx
        by_contra hnot
        have hz : infDist x sᶜ = 0 := infDist_zero_of_mem hnot
        exact hx (by simp [hz])
      · intro hx
        have hpos : 0 < infDist x sᶜ := (hs.isClosed_compl.notMem_iff_infDist_pos hne).mp
          (by simpa only [mem_compl_iff, not_not] using! hx)
        exact (lt_min (by norm_num : (0 : ℝ) < 1) hpos).ne'

theorem local_L2_agreement_on_open_overlap {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (s t : Set (Ambient d)) (hs : IsOpen s) (ht : IsOpen t)
    (f g : Ambient d → ℝ) (hf : MemLp f 2 (ν.restrict s)) (hg : MemLp g 2 (ν.restrict t))
    (w : ℕ → Ambient d → ℝ)
    (hfirst : ∀ (ψ : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith K ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j).restrict s) atTop
        (𝓝 (∫ x, f x * ψ x ∂ν.restrict s)))
    (hsecond : ∀ (ψ : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith K ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j).restrict t) atTop
        (𝓝 (∫ x, g x * ψ x ∂ν.restrict t))) :
    f =ᵐ[ν.restrict (s ∩ t)] g := by
  obtain ⟨χ, hχ, hbound, hsupp⟩ := exists_lipschitz_open_support (s ∩ t) (hs.inter ht)
  have hsupp' : ∀ x, χ x ≠ 0 ↔ x ∈ s ∩ t := by
    intro x
    change x ∈ support χ ↔ x ∈ s ∩ t
    rw [hsupp]
  apply local_L2_agreement_from_common_moments μ ν s t f g hf hg χ 1 1 hχ
    (fun x => by simpa only [abs_of_nonneg (hbound x).1, NNReal.coe_one] using! (hbound x).2)
    (fun x => (hsupp' x).mp) _ w hfirst hsecond
  filter_upwards [ae_restrict_mem (hs.inter ht).measurableSet] with x hx
  exact (hsupp' x).mpr hx

end

end RieszRectifiability

end OAI
