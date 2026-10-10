import Mathlib
import OAI.Probability.SKSupport.Regularity.RightRegularity
import OAI.Probability.SKSupport.Support.FiniteCDF
import OAI.Probability.SKSupport.Support.Closure

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

lemma extend_add_fun (f g : Time → ℝ) : extend (fun t => f t+g t)=fun t => extend f t+extend g t := by
  funext t
  by_cases ht : t ∈ Ico (0:ℝ) 1 <;> simp [extend,ht]
lemma extend_sub_fun (f g : Time → ℝ) : extend (fun t => f t-g t)=fun t => extend f t-extend g t := by
  funext t
  by_cases ht : t ∈ Ico (0:ℝ) 1 <;> simp [extend,ht]

def OrderParameter.addCDF (γ : OrderParameter) (ν : Measure Time) [IsFiniteMeasure ν] : OrderParameter where
  val := fun t => γ.val t+finiteCDF ν t
  nonneg := fun t => add_nonneg (γ.nonneg t) (finiteCDF_nonneg ν t)
  monotone := γ.monotone.add (finiteCDF_monotone ν)
  right_continuous := fun t => (γ.right_continuous t).add (finiteCDF_rightContinuous ν t)
  integrable := by rw [extend_add_fun];exact γ.integrable.add (finiteCDF_integrable ν)

lemma OrderParameter.addCDF_difference (γ : OrderParameter) (ν : Measure Time) [IsFiniteMeasure ν] (t : ℝ) :
    extend (γ.addCDF ν).val t-extend γ.val t=extend (finiteCDF ν) t := by
  change extend (fun t => γ.val t+finiteCDF ν t) t-extend γ.val t=_
  rw [extend_add_fun]
  ring

lemma stieltjes_real (γ : OrderParameter) {μ : Measure Time} (hμ : IsStieltjesMeasure γ μ) (t : Time) :
    (μ (Iic t)).toReal=γ.val t := by rw [hμ t,ENNReal.toReal_ofReal (γ.nonneg t)]

lemma finiteCDF_le_parameter (γ : OrderParameter) {μ ν : Measure Time} (hμ : IsStieltjesMeasure γ μ)
    (hν : ν ≤ μ) (t : Time) : finiteCDF ν t ≤ γ.val t := by
  rw [← stieltjes_real γ hμ t]
  apply ENNReal.toReal_mono
  · rw [hμ t];exact ENNReal.ofReal_ne_top
  · exact hν (Iic t)

lemma cdf_real_add_Ioc {μ : Measure Time} {a b : Time} (hab : a ≤ b) (hfinite : μ (Iic b) ≠ ⊤) :
    (μ (Iic a)).toReal+(μ (Ioc a b)).toReal=(μ (Iic b)).toReal := by
  have hf1 := ne_top_of_le_ne_top hfinite (measure_mono (Iic_subset_Iic.mpr hab))
  have hf2 := ne_top_of_le_ne_top hfinite (measure_mono (show Ioc a b ⊆ Iic b from fun _ h => h.2))
  have he : μ (Iic a)+μ (Ioc a b)=μ (Iic b) := by
    rw [← measure_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,Iic_union_Ioc_eq_Iic hab]
  have hh := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add hf1 hf2] at hh
  exact hh

lemma removeCDF_monotone (γ : OrderParameter) {μ ν : Measure Time} [IsFiniteMeasure ν]
    (hμ : IsStieltjesMeasure γ μ) (hν : ν ≤ μ) : Monotone (fun t => γ.val t-finiteCDF ν t) := by
  intro a b hab
  have hf : μ (Iic b) ≠ ⊤ := by rw [hμ b];exact ENNReal.ofReal_ne_top
  have hm := cdf_real_add_Ioc hab hf
  rw [stieltjes_real γ hμ a,stieltjes_real γ hμ b] at hm
  have hn := cdf_real_add_Ioc (μ := ν) hab (measure_ne_top ν _)
  have hi : (ν (Ioc a b)).toReal ≤ (μ (Ioc a b)).toReal :=
    ENNReal.toReal_mono (ne_top_of_le_ne_top hf (measure_mono (fun _ h => h.2))) (hν (Ioc a b))
  change γ.val a-(ν (Iic a)).toReal ≤ γ.val b-(ν (Iic b)).toReal
  linarith

def OrderParameter.removeCDF (γ : OrderParameter) {μ ν : Measure Time} [IsFiniteMeasure ν]
    (hμ : IsStieltjesMeasure γ μ) (hν : ν ≤ μ) : OrderParameter where
  val := fun t => γ.val t-finiteCDF ν t
  nonneg := fun t => sub_nonneg.mpr (finiteCDF_le_parameter γ hμ hν t)
  monotone := removeCDF_monotone γ hμ hν
  right_continuous := fun t => (γ.right_continuous t).sub (finiteCDF_rightContinuous ν t)
  integrable := by rw [extend_sub_fun];exact γ.integrable.sub (finiteCDF_integrable ν)

lemma OrderParameter.removeCDF_difference (γ : OrderParameter) {μ ν : Measure Time} [IsFiniteMeasure ν]
    (hμ : IsStieltjesMeasure γ μ) (hν : ν ≤ μ) (t : ℝ) :
    extend (γ.removeCDF hμ hν).val t-extend γ.val t= -extend (finiteCDF ν) t := by
  change extend (fun t => γ.val t-finiteCDF ν t) t-extend γ.val t=_
  rw [extend_sub_fun]
  ring

lemma OrderParameter.original_deterministic (γ : OrderParameter) :
    SupportDeterministic.IsOrderParameter (extend γ.val) where
  nonneg := fun t _ => γ.extend_nonneg t
  monotone := by
    intro a ha b hb hab
    simpa only [extend,dite_eq_left ha,dite_eq_left hb] using γ.monotone (show (⟨a,ha⟩ : Time) ≤ ⟨b,hb⟩ from hab)
  rightContinuous := by
    intro t ht
    let T : ℝ := (t+1)/2
    have hT0 : 0 ≤ T := by dsimp [T];linarith [ht.1,ht.2]
    have hT1 : T < 1 := by dsimp [T];linarith [ht.1,ht.2]
    have htT : t < T := by dsimp [T];linarith [ht.2]
    have hc := compactCoeff_rightContinuous γ hT0 hT1 t
    have he : compactCoeff γ T =ᶠ[𝓝[Ici t] t] extend γ.val := by
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htT)] with s hs hsT
      rw [compactCoeff,stripClamp_eq ⟨ht.1.trans hs,hsT.le⟩]
    have hh := hc.tendsto.congr' he
    change Tendsto (extend γ.val) (𝓝[Ici t] t) (𝓝 (extend γ.val t))
    simpa only [compactCoeff,stripClamp_eq ⟨ht.1,htT.le⟩] using hh
  integrable := γ.integrable.integrableOn

lemma stieltjes_deterministic (γ : OrderParameter) {μ : Measure Time} (hμ : IsStieltjesMeasure γ μ) :
    SupportDeterministic.IsStieltjesMeasure (extend γ.val) μ := by
  intro t
  simpa only [extend,dite_eq_left t.property] using hμ t

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

lemma finiteCDF_fubini {H : ℝ → ℝ} (hH : IntervalIntegrable H volume 0 1)
    (ν : Measure Time) [IsFiniteMeasure ν] :
    (∫ t in (0:ℝ)..1, extend (finiteCDF ν) t*H t)=∫ r : Time, (∫ t in (r:ℝ)..1, H t) ∂ν := by
  let κ : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1)
  let F : ℝ → Time → ℝ := fun t r => if (r:ℝ) ≤ t then H t else 0
  have hHi : Integrable H κ := hH.1
  have hs : MeasurableSet {p : ℝ × Time | (p.2:ℝ) ≤ p.1} :=
    (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_fst).measurableSet
  have hFi : Integrable (Function.uncurry F) (κ.prod ν) := by
    have he : Function.uncurry F = {p : ℝ × Time | (p.2:ℝ) ≤ p.1}.indicator (fun p => H p.1) := by
      funext p
      rfl
    rw [he]
    exact (hHi.comp_fst ν).indicator hs
  have hleft : (∫ t in (0:ℝ)..1, extend (finiteCDF ν) t*H t)=∫ t, ∫ r, F t r ∂ν ∂κ := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with t ht ht1
    have htt : t ∈ Ico (0:ℝ) 1 := ⟨ht.1.le,lt_of_le_of_ne ht.2 ht1⟩
    rw [extend,dite_eq_left htt,finiteCDF_integral,← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with r
    change (if r ≤ (⟨t,htt⟩ : Time) then (1:ℝ) else 0)*H t=(if (r:ℝ) ≤ t then H t else 0)
    by_cases hr : (r:ℝ) ≤ t <;> simp [hr,show (r ≤ (⟨t,htt⟩ : Time)) ↔ (r:ℝ) ≤ t from Iff.rfl]
  have hright (r : Time) : (∫ t, F t r ∂κ)=∫ t in (r:ℝ)..1, H t := by
    have he : (∫ t, F t r ∂κ)=∫ t, (Ioi (r:ℝ)).indicator H t ∂κ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (volume.ae_ne (r:ℝ))] with t htr
      simp only [F,indicator_apply,mem_Ioi]
      simp only [le_iff_lt_or_eq,or_iff_left (Ne.symm htr)]
    rw [he,integral_indicator measurableSet_Ioi]
    change (∫ t, H t ∂((volume.restrict (Ioc (0:ℝ) 1)).restrict (Ioi (r:ℝ))))=_
    rw [Measure.restrict_restrict measurableSet_Ioi]
    have heS : Ioi (r:ℝ) ∩ Ioc (0:ℝ) 1=Ioc (r:ℝ) 1 := by
      ext t
      simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
      constructor
      · exact fun h => ⟨h.1,h.2.2⟩
      · exact fun h => ⟨h.1,lt_of_le_of_lt r.property.1 h.1,h.2⟩
    rw [heS,intervalIntegral.integral_of_le r.property.2.le]
  rw [hleft,integral_integral_swap hFi]
  exact integral_congr_ae (Eventually.of_forall hright)

end ZeroTemperatureSK

end
end

end OAI
