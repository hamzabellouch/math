import OAI.Probability.InvariantIsing.Gaussian.GaussianSingularLowerMean
import OAI.Probability.InvariantIsing.Gaussian.GaussianTranspose
import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternAspect

namespace OAI

/-! The lower singular edge of the transposed physical Gaussian array. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma gaussianPatternCount_sub_one_ratio_tendsto {α : ℝ} (hα : 0 ≤ α) :
    Tendsto (fun k : ℕ => ((gaussianPatternCount α (k+1) : ℝ)-1)/(k+1)) atTop (𝓝 α) := by
  have h := (gaussianPatternCount_ratio_tendsto hα).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [sub_zero,sub_div] using h

theorem gaussianPatternTranspose_lower_edge {α : ℝ} (hα : 0 < α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω => max (Real.sqrt α-1-
      gaussianPatternSingularMin (gaussianPatternTranspose (k+1) (gaussianPatternCount α (k+1))
        (Z (k+1) ω))/Real.sqrt (k+1)) 0) atTop (fun _ => 0) := by
  let T (k : ℕ) (ω : Ω) :=
    gaussianPatternTranspose (k+1) (gaussianPatternCount α (k+1)) (Z (k+1) ω)
  let M (k : ℕ) := ∫ z : EuclideanSpace ℝ (Fin (gaussianPatternCount α (k+1)) × Fin (k+1)),
    gaussianPatternSingularMin z ∂stdGaussian _
  let B (k : ℕ) := Real.sqrt (((gaussianPatternCount α (k+1) : ℝ)-1)/(k+1))-1
  have hB : Tendsto B atTop (𝓝 (Real.sqrt α-1)) :=
    ((Real.continuous_sqrt.tendsto α).comp (gaussianPatternCount_sub_one_ratio_tendsto hα.le)).sub_const 1
  have hpos : ∀ᶠ k : ℕ in atTop, 0 < gaussianPatternCount α (k+1) := by
    filter_upwards [(tendsto_order.1 (gaussianPatternCount_ratio_tendsto hα.le)).1 0 hα] with k hk
    have hp : (0 : ℝ) < (gaussianPatternCount α (k+1) : ℝ) :=
      (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < k+1)).mp hk
    exact_mod_cast hp
  have hM : ∀ᶠ k : ℕ in atTop, B k ≤ M k/Real.sqrt (k+1) := by
    filter_upwards [hpos] with k hk
    have hh := gaussianPatternSingularMin_mean_ge hk (Nat.succ_pos k)
    have hs : 0 < Real.sqrt (k+1 : ℝ) := by positivity
    have hc : (0 : ℝ) ≤ (gaussianPatternCount α (k+1) : ℝ)-1 := by
      have hc' : (1 : ℝ) ≤ (gaussianPatternCount α (k+1) : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hk)
      linarith
    have hd := div_le_div_of_nonneg_right hh hs.le
    dsimp only [B,M]
    rw [Real.sqrt_div hc]
    simpa only [Nat.cast_succ,Nat.cast_add,Nat.cast_one,sub_div,div_self hs.ne'] using hd
  have hT (k : ℕ) : HasLaw (T k) (stdGaussian _) P := gaussianPatternTranspose_hasLaw P _ (hZ (k+1))
  have hcent := finiteGaussian_centered_tendsto (fun k =>
      gaussianPatternSingularMin (N := gaussianPatternCount α (k+1)) (m := k+1))
    (fun k => gaussianPatternSingularMin_lipschitz _ _ (Nat.succ_pos k)) P T hT
  have hmeas (k : ℕ) : AEStronglyMeasurable
      (fun ω => max (Real.sqrt α-1-gaussianPatternSingularMin (T k ω)/Real.sqrt (k+1)) 0) P := by
    have h : Measurable (fun z : EuclideanSpace ℝ
        (Fin (gaussianPatternCount α (k+1)) × Fin (k+1)) =>
        max (Real.sqrt α-1-gaussianPatternSingularMin z/Real.sqrt (k+1)) 0) := by
      have hc := (gaussianPatternSingularMin_lipschitz (gaussianPatternCount α (k+1)) (k+1)
        (Nat.succ_pos k)).continuous
      fun_prop
    exact (h.aemeasurable.comp_aemeasurable (hT k).aemeasurable).aestronglyMeasurable
  apply (exists_seq_tendstoInMeasure_atTop_iff hmeas).mpr
  intro ns hns
  obtain ⟨u,hu,hcu⟩ := (hcent.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨u,hu,?_⟩
  filter_upwards [hcu] with ω hω
  have hc : Tendsto (fun k => (gaussianPatternSingularMin (T (ns (u k)) ω)-M (ns (u k)))/
      Real.sqrt (ns (u k)+1)) atTop (𝓝 0) := hω
  have hb := hB.comp (hns.comp hu).tendsto_atTop
  have ht := ((hc.neg.add (tendsto_const_nhds (x := Real.sqrt α-1))).sub hb).max
    (tendsto_const_nhds (x := (0 : ℝ)))
  have ht' : Tendsto (fun k => max
      (-(gaussianPatternSingularMin (T (ns (u k)) ω)-M (ns (u k)))/Real.sqrt (ns (u k)+1) +
        (Real.sqrt α-1)-B (ns (u k))) 0) atTop (𝓝 0) := by
    simpa only [neg_zero,zero_add,sub_self,max_self,neg_div,Function.comp_def] using ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => le_max_right _ _)) _ ht'
  filter_upwards [(hns.comp hu).tendsto_atTop.eventually hM] with k hk
  dsimp only [Function.comp_def] at hk
  apply max_le_max _ le_rfl
  rw [neg_div,sub_div]
  linarith

end InvariantIsing

end

end OAI
