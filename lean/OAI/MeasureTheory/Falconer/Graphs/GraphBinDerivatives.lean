import OAI.MeasureTheory.Falconer.Graphs.GraphActualMixedDerivatives
import OAI.MeasureTheory.Falconer.Angular.SelectedAngularBins

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

theorem graph_selected_bins_mixed (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 2*Real.pi →
      ∀ (S : Finset ℕ) (plus : Bool) (c : ℝ) (η : Plane) (z : ℝ),
      ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ →
      ‖iteratedFDeriv ℝ n (graphAngularPullback
        (fun θ => ((∑ k ∈ S, periodicAngularBin (angularBinCount δ) k θ : ℝ):ℂ)) plus c) (η,z)‖ ≤
        A * (max 1 δ⁻¹)^n := by
  choose C hC hbound using fun j => selectedAngularBins_scale_derivatives j
  let B : ℝ := ∑ j ∈ Finset.range (n+1), C j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hC j)
  obtain ⟨A,hA,hcomp⟩ := graph_mixed_composition_scale n
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro δ hδ hcap S plus c η z hhi hz hlo
  have hf : ContDiff ℝ ∞ (fun θ => ∑ k ∈ S, periodicAngularBin (angularBinCount δ) k θ) := by
    apply ContDiff.sum
    intro k _
    exact periodicAngularBin_contDiff _ _
  apply hcomp _ (Complex.ofRealCLM.contDiff.comp hf) _ B (max 1 δ⁻¹) hB (le_max_left _ _) _
    plus c η z hhi hz hlo
  · intro θ
    change ((∑ k ∈ S, periodicAngularBin (angularBinCount δ) k (θ+2*Real.pi) : ℝ):ℂ) = _
    apply congrArg Complex.ofReal
    apply Finset.sum_congr rfl
    intro k _
    exact periodicAngularBin_periodic _ _ θ
  · intro j hj θ
    change ‖iteratedDeriv j (fun t => ((∑ k ∈ S, periodicAngularBin (angularBinCount δ) k t : ℝ):ℂ)) θ‖ ≤ _
    rw [iteratedDeriv_ofReal hf, Complex.norm_real]
    apply (hbound j δ hδ hcap S θ).trans
    apply mul_le_mul
    · exact Finset.single_le_sum (fun l _ => hC l)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    · exact pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
    · positivity
    · exact hB

end PlanarFalconer

end OAI
