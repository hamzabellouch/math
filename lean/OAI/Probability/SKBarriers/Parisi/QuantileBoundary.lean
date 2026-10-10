import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileVariation

namespace OAI

section

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SK.Analytic

theorem quantileOverlapMean_continuous (k : ℕ) (β : ℝ) :
    Continuous (quantileOverlapMean k β) := by
  have hv : Continuous (fun Q : Fin (k+1) → ℝ => fun b => Real.sqrt (cumulativeGapMap k Q b)) := by
    apply continuous_pi
    intro b
    exact Real.continuous_sqrt.comp ((continuous_apply b).comp (cumulativeGapMap k).continuous)
  have H := (blockAdaptiveOverlap_contDiff (k := k) (skInteraction 1) (fun _ => (0:ℝ)) β).continuous.comp
    ((continuous_const (y := (0:ℝ))).prodMk hv)
  have he : quantileOverlapMean k β = fun Q =>
      blockAdaptiveOverlap (k := k) (skInteraction 1) (fun _ => (0:ℝ)) β
        (0,fun b => Real.sqrt (cumulativeGapMap k Q b)) := by
    funext Q j
    simp only [quantileOverlapMean,blockAdaptiveOverlap,mul_zero]
  rw [he]
  exact H

theorem extendedQuantileParisi_hasDerivWithinAt_segment {k : ℕ} (β : ℝ)
    (A B : Fin (k+1) → ℝ) (hA : ∀ j, 0 ≤ cumulativeGapMap k A j)
    (hB : ∀ j, 0 < cumulativeGapMap k B j) :
    HasDerivWithinAt (fun t : ℝ => extendedQuantileParisi k β ((1-t) • A+t • B))
      ((β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(B j-A j)*
        (A j-quantileOverlapMean k β A j)) (Set.Ici 0) 0 := by
  let Q := fun t : ℝ => (1-t) • A+t • B
  let d := fun t => (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(B j-A j)*
    (Q t j-quantileOverlapMean k β (Q t) j)
  have hQ (t : ℝ) : HasDerivAt Q (B-A) t := by
    apply hasDerivAt_pi.mpr
    intro j
    have H := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul_const (A j)).add
      ((hasDerivAt_id t).mul_const (B j))
    exact H.congr_deriv (by simp; ring)
  have hQc : Continuous Q := continuous_iff_continuousAt.mpr (fun t => (hQ t).continuousAt)
  have hdc : Continuous d := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul (((continuous_apply j).comp hQc).sub
      ((continuous_apply j).comp ((quantileOverlapMean_continuous k β).comp hQc)))
  have hd (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
      HasDerivAt (fun t => extendedQuantileParisi k β (Q t)) (d t) t := by
    apply extendedQuantileParisi_hasDerivAt β Q (hQ t)
    intro j
    simp only [Q,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2.le) (hA j))
      (mul_pos ht.1 (hB j))
  have hs : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by norm_num)
  have he : (fun t => deriv (fun t => extendedQuantileParisi k β (Q t)) t) =ᶠ[𝓝[>] (0:ℝ)] d := by
    filter_upwards [hs] with t ht
    exact (hd t ht).deriv
  have H := hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (((extendedQuantileParisi_continuous k β).comp hQc).continuousAt.continuousWithinAt)
    hs ((hdc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
  simpa only [d,Q,sub_zero,one_smul,zero_smul,add_zero] using H

end SK.Analytic

end
end

end

end OAI
