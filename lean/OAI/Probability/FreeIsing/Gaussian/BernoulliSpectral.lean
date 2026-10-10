import OAI.Probability.FreeIsing.Estimates.CenteredLocalDensity
import OAI.Probability.FreeIsing.Estimates.LocalCorrelation
import OAI.Probability.FreeIsing.Spectral.RadialPowerGrowth
import OAI.Probability.FreeIsing.Spectral.SpectralTransfer
import OAI.Probability.FreeIsing.Trees.WordAction

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeKoopman

theorem local_average_power_bound {d : ℕ} (hd : 3 ≤ d)
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 (labelMeasure d))
    (F : (s → ℝ) → ℝ) (hF : Measurable F)
    (hf : f =ᵐ[labelMeasure d] fun U => F (fun i => U i))
    (hzero : (∫ U, f U ∂labelMeasure d) = 0) :
    ∃ C : ℝ, ∀ n : ℕ, ‖(average d ^ n) f‖ ≤ C * RadialWalk.rate d ^ n := by
  obtain ⟨C, hC, hcov⟩ := exists_local_koopman_critical_bound hd s f F hF hf hzero
  have hword (v : TreeVertex d) :
      |inner ℝ f (RadialWalk.wordOperator generatorOperator v f)| ≤
        C * RadialWalk.treeWeight d v := by
    have hdepth : ((wordAut v.1).symm.toEquiv TreeEscape.root).1.length =
        v.1.length := by
      change ((wordAut v.1).toEquiv.symm TreeEscape.root).1.length = _
      rw [TreeEscape.symm_root_depth]
      rw [wordAut_root v.1 v.2]
    simpa only [wordOperator_eq, wordRelabel, RadialWalk.treeWeight,
      RadialWalk.weight, hdepth] using hcov (wordAut v.1).symm
  have hsym : (RadialWalk.operatorAverage (generatorOperator (d := d)) :
      Lp ℝ 2 (labelMeasure d) →ₗ[ℝ] Lp ℝ 2 (labelMeasure d)).IsSymmetric := by
    rw [operatorAverage_eq]
    exact (average_selfAdjoint d).isSymmetric
  refine ⟨Real.sqrt C, fun n => ?_⟩
  simpa only [operatorAverage_eq] using
    RadialWalk.norm_power_le_of_radial_bound generatorOperator generatorOperator_sq
      hsym hd f hC hword n

theorem centeredAverage_norm_le {d : ℕ} (hd : 3 ≤ d) :
    ‖centeredAverage d‖ ≤ 2 * Real.sqrt ((d : ℝ) - 1) / d := by
  apply selfAdjoint_opNorm_le_of_dense_power_bound (centeredAverage d)
    (centeredAverage_selfAdjoint d) (RadialWalk.rate_nonneg d)
    (dense_centered_finite_coordinate (labelMeasure d))
  intro f hf
  obtain ⟨s, F, hF, hf⟩ := hf
  obtain ⟨C, hC⟩ := local_average_power_bound hd s (f : Lp ℝ 2 (labelMeasure d))
    F hF hf ((mem_centeredL2_iff _).mp f.property)
  refine ⟨C, fun n => ?_⟩
  change ‖((centeredAverage d ^ n) f : Lp ℝ 2 (labelMeasure d))‖ ≤ _
  rw [centeredAverage_pow_apply_coe]
  exact hC n

end Problem367.TreeKoopman

end

end OAI
