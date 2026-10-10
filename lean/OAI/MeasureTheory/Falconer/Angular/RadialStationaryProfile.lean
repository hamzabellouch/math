import OAI.MeasureTheory.Falconer.Angular.AngularRadialKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

noncomputable def radialStationaryProfile (Ψ : ℝ → ℝ) (p : ℝ) (s : ℝ) : ℂ :=
  (Ψ s * s^p : ℝ)

theorem radialStationaryProfile_contDiff {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (p : ℝ) :
    ContDiff ℝ ∞ (radialStationaryProfile Ψ p) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hz : s = 0
  · subst s
    have he : radialStationaryProfile Ψ p =ᶠ[𝓝 0] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds (by norm_num : (0:ℝ) < 1/4)] with t ht
      have ht0 : Ψ t = 0 := by
        by_contra hn
        exact (not_lt_of_ge (hs t hn).1.le) ht
      simp [radialStationaryProfile,ht0]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp s
      (hΨ.contDiffAt.mul (contDiffAt_id.rpow_const_of_ne hz))

theorem radialStationaryProfile_tsupport {Ψ : ℝ → ℝ}
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (p : ℝ) :
    tsupport (radialStationaryProfile Ψ p) ⊆ Icc (1/4:ℝ) 4 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  have hn : Ψ t ≠ 0 := by
    intro hz
    exact ht (by simp [radialStationaryProfile,hz])
  exact Ioo_subset_Icc_self (hs t hn)

theorem compact_complex_derivatives_bounded {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {K : Set ℝ} (hK : IsCompact K) (hs : tsupport f ⊆ K) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ n, ∀ s, ‖iteratedDeriv j f s‖ ≤ C := by
  have hc (j : ℕ) : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j (WithTop.coe_le_coe.mpr (show (j:ℕ∞) ≤ ⊤ from le_top))
  choose C hC using fun j => hK.exists_bound_of_continuousOn (hc j).continuousOn
  let B := ∑ j ∈ Finset.range (n+1), max 0 (C j)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  refine ⟨B,hB,?_⟩
  intro j hj s
  by_cases hmem : s ∈ K
  · apply (hC j s hmem).trans
    apply (le_max_right 0 (C j)).trans
    exact Finset.single_le_sum (fun _ _ => le_max_left _ _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  · have hz : iteratedDeriv j f s = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hmem (hs (complex_iteratedDeriv_tsupport f j ht)))
    simpa only [hz,norm_zero] using hB

theorem radialStationaryProfile_derivatives {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (p : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ n, ∀ s, ‖iteratedDeriv j (radialStationaryProfile Ψ p) s‖ ≤ C :=
  compact_complex_derivatives_bounded (radialStationaryProfile_contDiff hΨ hs p)
    isCompact_Icc (radialStationaryProfile_tsupport hs p) n

end PlanarFalconer

end OAI
