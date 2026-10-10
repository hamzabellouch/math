import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternAspect

namespace OAI

/-! The sharp one-sided upper singular-value edge for the actual rectangular Gaussian model. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem gaussianPatternSingularMax_upper_edge {α : ℝ} (hα : 0 ≤ α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω =>
      max (gaussianPatternSingularMax (Z (k+1) ω)/Real.sqrt (k+1) - (1+Real.sqrt α)) 0)
      atTop (fun _ => 0) := by
  let M (k : ℕ) := ∫ z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))),
    gaussianPatternSingularMax z ∂stdGaussian _
  let B (k : ℕ) := 1+Real.sqrt ((gaussianPatternCount α (k+1) : ℝ)/(k+1))
  have hB : Tendsto B atTop (𝓝 (1+Real.sqrt α)) := gaussianPatternCount_sqrt_ratio_tendsto hα
  have hM (k : ℕ) : M k/Real.sqrt (k+1) ≤ B k := by
    simpa only [Nat.cast_succ,Nat.cast_add,Nat.cast_one] using
      gaussianPattern_mean_div_sqrt_le (m := gaussianPatternCount α (k+1)) (Nat.succ_pos k)
  have hmeas (k : ℕ) : AEStronglyMeasurable
      (fun ω => max (gaussianPatternSingularMax (Z (k+1) ω)/Real.sqrt (k+1) -
        (1+Real.sqrt α)) 0) P := by
    have hc := (gaussianPatternSingularMax_lipschitz (k+1) (gaussianPatternCount α (k+1))).continuous
    have hm : Measurable (fun z : EuclideanSpace ℝ (Fin (k+1) × Fin (gaussianPatternCount α (k+1))) =>
        max (gaussianPatternSingularMax z/Real.sqrt (k+1)-(1+Real.sqrt α)) 0) := by fun_prop
    exact (hm.aemeasurable.comp_aemeasurable (hZ (k+1)).aemeasurable).aestronglyMeasurable
  apply (exists_seq_tendstoInMeasure_atTop_iff hmeas).mpr
  intro ns hns
  obtain ⟨u,hu,hcu⟩ := ((gaussianPatternSingularMax_centered_tendsto
    (fun k => gaussianPatternCount α (k+1)) P (fun k => Z (k+1))
    (fun k => hZ (k+1))).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨u,hu,?_⟩
  filter_upwards [hcu] with ω hω
  have hc : Tendsto (fun k =>
      (gaussianPatternSingularMax (Z (ns (u k)+1) ω)-M (ns (u k)))/Real.sqrt (ns (u k)+1))
      atTop (𝓝 0) := hω
  have hb := hB.comp (hns.comp hu).tendsto_atTop
  have ht := ((hc.add hb).sub_const (1+Real.sqrt α)).max (tendsto_const_nhds (x := (0 : ℝ)))
  have ht' : Tendsto (fun k => max
      ((gaussianPatternSingularMax (Z (ns (u k)+1) ω)-M (ns (u k)))/Real.sqrt (ns (u k)+1) +
        B (ns (u k))-(1+Real.sqrt α)) 0) atTop (𝓝 0) := by
    simpa only [zero_add,sub_self,max_self,Function.comp_def] using ht
  apply squeeze_zero (fun _ => le_max_right _ _) _ ht'
  intro k
  apply max_le_max _ le_rfl
  have hm := hM (ns (u k))
  rw [sub_div]
  linarith

end InvariantIsing

end

end OAI
