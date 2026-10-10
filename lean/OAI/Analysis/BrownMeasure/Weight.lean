import Mathlib
import OAI.Analysis.BrownMeasure.Model
import OAI.Analysis.FiniteFactor.Matrix.Entries
import OAI.Analysis.FiniteFactor.OrbitSampling.Measures

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace FiniteFactor

def productWeightValues : Set ℝ := Set.range (fun a : SourceCoordinate →₀ ℤ =>
  Real.exp (-(∑' i,sourceLogWeight i * (a i:ℝ))))
lemma productWeightValues_countable : productWeightValues.Countable := Set.countable_range _
lemma sourceCocycle_mem_values (θ : SourceCoordinate → ℝ) {x : SourceCoordinate → ℝ}
    (hx : finiteFloorSupport θ x) (k : ℤ) : sourceCocycle θ sourceLogWeight k x∈productWeightValues := by
  refine ⟨Finsupp.ofSupportFinite (coordinateFloor θ k x) (hx k),?_⟩
  simp only [sourceCocycle,sourceLog,Finsupp.ofSupportFinite_coe]
lemma sourceWeight_ae_countable (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    ∀ᵐ x ∂sourceBaseMeasure,sourceCocycle θ sourceLogWeight 1 x∈productWeightValues :=
  (ae_finiteFloorSupport θ hθ.summable).mono (fun _ h=>sourceCocycle_mem_values θ h 1)

lemma SourceAngles.lt_one {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) (i : SourceCoordinate) : θ i<1 := by
  have hm : (100:ℝ)≤ sourceBlockSize i.1 := by exact_mod_cast (sourceStage i.1).m_ge_100
  have hK : (1:ℝ)≤(sourceStageState i.1).K := by exact_mod_cast (sourceStageState i.1).K_ge
  apply (hθ i).2.trans_lt
  apply (div_lt_one (mul_pos (sourceBlockSize_pos _) (sourceCutoff_pos _))).mpr
  change (2 : ℝ) < (sourceBlockSize i.1 : ℝ) * (sourceStageState i.1).K
  nlinarith

lemma unitInterval_floor_lintegral (a c : ℝ) (ha : 0≤a) (ha1 : a≤1) (hc : 0≤c) :
    (∫⁻ t,ENNReal.ofReal (c*(Int.floor (t+a):ℝ)) ∂unitIntervalMeasure)=ENNReal.ofReal (c*a) := by
  classical
  have he : (fun t=>ENNReal.ofReal (c*(Int.floor (t+a):ℝ))) =ᵐ[unitIntervalMeasure]
      (Set.Ico (1-a) 1).indicator (fun _=>ENNReal.ofReal c) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    rcases ht with ⟨ht0,ht1⟩
    by_cases hlt : t<1-a
    · have hz : Int.floor (t+a)=0 := Int.floor_eq_zero_iff.mpr ⟨by linarith,by linarith⟩
      have hn : t∉Set.Ico (1-a) 1 := fun h=>not_le_of_gt hlt h.1
      simp [hz,Set.indicator_of_notMem hn]
    · have ho : Int.floor (t+a)=1 := by
        apply Int.floor_eq_iff.mpr
        constructor <;> push_cast <;> linarith
      have hh : t∈Set.Ico (1-a) 1 := ⟨le_of_not_gt hlt,ht1⟩
      simp [ho,Set.indicator_of_mem hh]
  rw [lintegral_congr_ae he,lintegral_indicator measurableSet_Ico,lintegral_const]
  rw [Measure.restrict_apply_univ]
  have hs : Set.Ico (1-a) 1⊆Set.Ico (0:ℝ) 1 := by intro t ht; exact ⟨by linarith [ht.1],ht.2⟩
  rw [unitIntervalMeasure,Measure.restrict_apply measurableSet_Ico,Set.inter_eq_left.mpr hs,Real.volume_Ico]
  rw [show (1:ℝ)-(1-a)=a by ring,ENNReal.ofReal_mul hc]

lemma source_coordinate_log_integral (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (i : SourceCoordinate) :
    (∫⁻ x,ENNReal.ofReal (sourceLogWeight i*(coordinateFloor θ 1 x i:ℝ)) ∂sourceBaseMeasure)=
      ENNReal.ofReal (sourceLogWeight i*θ i) := by
  have hm : Measurable (fun t : ℝ=>ENNReal.ofReal (sourceLogWeight i*(Int.floor (t+θ i):ℝ))) := by fun_prop
  have he := lintegral_map (μ := sourceBaseMeasure) hm (measurable_pi_apply i)
  rw [Measure.infinitePi_map_eval] at he
  simpa only [Function.comp_def,coordinateFloor,Int.cast_one,one_mul] using
    he.symm.trans (unitInterval_floor_lintegral (θ i) (sourceLogWeight i) (hθ.nonneg i)
      (hθ.lt_one i).le (sourceLogWeight_nonneg i))

lemma sourceLog_nonneg (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {x : SourceCoordinate → ℝ} (hx : ∀ i,x i∈Set.Ico 0 1) : 0≤ sourceLog θ sourceLogWeight 1 x := by
  apply tsum_nonneg
  intro i
  apply mul_nonneg (sourceLogWeight_nonneg i)
  change 0 ≤ (Int.floor (x i + ((1:ℤ):ℝ)*θ i):ℝ)
  simp only [Int.cast_nonneg_iff, Int.floor_nonneg, Int.cast_one, one_mul]
  exact add_nonneg (hx i).1 (hθ.nonneg i)

lemma sourceLog_lintegral_prefix (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (s : Finset SourceCoordinate) :
    ENNReal.ofReal (∑ i∈s,sourceLogWeight i*θ i)≤
      ∫⁻ x,ENNReal.ofReal (sourceLog θ sourceLogWeight 1 x) ∂sourceBaseMeasure := by
  classical
  have hnonneg (i : SourceCoordinate) : 0≤ sourceLogWeight i*θ i := mul_nonneg (sourceLogWeight_nonneg i) (hθ.nonneg i)
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _=>hnonneg i)]
  simp_rw [← source_coordinate_log_integral θ hθ]
  rw [← lintegral_finsetSum _ (fun i _=> by unfold coordinateFloor; fun_prop)]
  apply lintegral_mono_ae
  filter_upwards [ae_finiteFloorSupport θ hθ.summable,sourceSamplingHaar_cube] with x hx hcube
  have hnn (i : SourceCoordinate) : 0≤ sourceLogWeight i*(coordinateFloor θ 1 x i:ℝ) := by
    apply mul_nonneg (sourceLogWeight_nonneg i)
    change 0 ≤ (Int.floor (x i + ((1:ℤ):ℝ)*θ i):ℝ)
    simp only [Int.cast_nonneg_iff, Int.floor_nonneg, Int.cast_one, one_mul]
    exact add_nonneg (hcube i).1 (hθ.nonneg i)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _=>hnn i)]
  exact ENNReal.ofReal_le_ofReal ((sourceLog_summable θ sourceLogWeight hx 1).sum_le_tsum s (fun i _=>hnn i))

theorem sourceLog_lintegral_top (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    (∫⁻ x,ENNReal.ofReal (sourceLog θ sourceLogWeight 1 x) ∂sourceBaseMeasure)=∞ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro a
  obtain ⟨q,hq⟩ := (hθ.weighted_prefix_diverges.eventually (eventually_ge_atTop (a:ℝ))).exists
  exact (show (a:ℝ≥0∞)≤ENNReal.ofReal (∑ i∈CouplingParameters.blockPrefix sourceBlockSize q,sourceLogWeight i*θ i) by
    simpa using ENNReal.ofReal_le_ofReal hq).trans (sourceLog_lintegral_prefix θ hθ _)
end FiniteFactor
end

end OAI
