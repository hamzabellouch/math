import Mathlib
import OAI.Probability.Ballisticity.Estimates.ScaledMaxTail

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

theorem small_scale_tail_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrinf : Tendsto r atTop atTop)
    (F : ℕ → ℝ) {F₀ : ℝ} (hF₀ : 0 < F₀) (hFle : ∀ j, F₀ ≤ F j)
    (hFlim : Tendsto F atTop (𝓝 F₀))
    (hF : ∀ j, Tendsto (fun n => truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (dyadicCut j*r n)/
      truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r n)) atTop (𝓝 (F j)))
    {A : ℝ} (hA : 0 < A) (B : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    let μ := independentConditionedPairLaw ν ℓ
    let S := commonIncrementProcess ℓ f 0
    ∀ᶠ j in atTop,
      limsup (fun n => cappedTailMoment (successfulAverage ν ℓ ⌊fluctuationScale μ S (dyadicCut j*r n)⌋₊)
        (fun X => medianDeviation ℓ f (fun h => (recordMedian ν ℓ hp f h:ℝ))
          ⌊fluctuationScale μ S (dyadicCut j*r n)⌋₊ X/(dyadicCut j*r n)) A (dyadicCut B/dyadicCut j)) atTop ≤
      (16000/p^2)*(2048/(A/40)^2+16*(F B/F₀-1))+δ := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  let μ := independentConditionedPairLaw ν ℓ
  let S := commonIncrementProcess ℓ f 0
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ hp
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hm (n) : truncatedVariance μ S (r n) ≠ 0 :=
    ne_of_gt (truncatedVariance_pos μ S (measurable_commonIncrementProcess ℓ f 0) hne (hr n))
  have hlim : Tendsto (fun j => (16000/p^2)*(2048/(A/40)^2+16*(F B/F j-1)+(64/3)*(1-F (j+1)/F j)))
      atTop (𝓝 ((16000/p^2)*(2048/(A/40)^2+16*(F B/F₀-1)))) := by
    have hsucc : Tendsto (fun j => F (j+1)) atTop (𝓝 F₀) := hFlim.comp (tendsto_add_atTop_nat 1)
    have hRlim := (tendsto_const_nhds (x := F B)).div hFlim (ne_of_gt hF₀)
    have hGlim := hsucc.div hFlim (ne_of_gt hF₀)
    have hh := (((tendsto_const_nhds (x := 2048/(A/40)^2)).add
      ((hRlim.sub_const 1).const_mul 16)).add
        (((tendsto_const_nhds (x := (1:ℝ))).sub hGlim).const_mul (64/3))).const_mul (16000/p^2)
    simpa only [Pi.div_apply,div_self (ne_of_gt hF₀),sub_self,mul_zero,add_zero] using hh
  have hsmall := dyadicCut_tendsto.eventually (gt_mem_nhds (div_pos (dyadicCut_pos B) hA))
  filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ hδ)),hsmall,eventually_ge_atTop B]
    with j hj hsj hBj
  have hj0 := dyadicCut_pos j
  have hAL : A < dyadicCut B/dyadicCut j := by
    rw [lt_div_iff₀ hj0]
    have := (lt_div_iff₀ hA).mp hsj
    nlinarith
  have hL : 1 ≤ dyadicCut B/dyadicCut j := (one_le_div hj0).mpr (dyadicCut_antitone hBj)
  have hFj : F j ≠ 0 := ne_of_gt (hF₀.trans_le (hFle j))
  let z := fun n => dyadicCut j*r n
  have hz : ∀ n, 0 < z n := fun n => mul_pos hj0 (hr n)
  have hzinf : Tendsto z atTop atTop := hrinf.const_mul_atTop hj0
  have hR : Tendsto (fun n => truncatedVariance μ S ((dyadicCut B/dyadicCut j)*z n)/
      truncatedVariance μ S (z n)) atTop (𝓝 (F B/F j)) := by
    convert (hF B).div (hF j) hFj using 1
    funext n
    have heq : (dyadicCut B/dyadicCut j)*z n = dyadicCut B*r n := by
      dsimp [z]; field_simp
    rw [heq]
    simp only [Pi.div_apply]
    change _ = (truncatedVariance μ S _/truncatedVariance μ S (r n))/(truncatedVariance μ S (z n)/truncatedVariance μ S (r n))
    field_simp [hm n]
  have hG : Tendsto (fun n => truncatedVariance μ S (z n/2)/truncatedVariance μ S (z n))
      atTop (𝓝 (F (j+1)/F j)) := by
    convert (hF (j+1)).div (hF j) hFj using 1
    funext n
    rw [dyadicCut_succ]
    have heq : z n/2 = (dyadicCut j/2)*r n := by dsimp [z]; ring
    rw [heq]
    simp only [Pi.div_apply]
    change _ = (truncatedVariance μ S _/truncatedVariance μ S (r n))/(truncatedVariance μ S (z n)/truncatedVariance μ S (r n))
    field_simp [hm n]
  have hH : Tendsto (fun n => ⌊fluctuationScale μ S (z n)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (recordFluctuationScale_tendsto ν hue e f hef htrans z hzinf)
  have hbound := successful_tail_profile_bound ν hue e f hef htrans z hz hzinf _ hH hA hAL hL
    (Eventually.of_forall fun n => Nat.floor_le (fluctuationScale_nonneg μ S (z n))) hR hG
  exact hbound.trans hj.le

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma success_medianTube_curveIncrement {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hp : annealedLaw ν (NoDrop (realPosition (step e)) 0) ≠ 0)
    (x : Lattice d) {H : ℕ} (hH : 0 < H) (B R : ℝ) (ω : Environment d) :
    successQuenchedKernel (realPosition (step e)) x H ω
      (medianTubeEndpoint ν (realPosition (step e)) hp f x H B R) =
    (crossingQuenched (realPosition (step e)) x H ω)⁻¹*
      curveIncrement (realPosition (step e)) f x
        (fun j => (recordMedian ν (realPosition (step e)) hp f j:ℝ)) B H ω
        {u | |signedCoordinate f u-(recordMedian ν (realPosition (step e)) hp f H:ℝ)| ≤ R} := by
  let ℓ := realPosition (step e)
  let b := fun j => (recordMedian ν ℓ hp f j:ℝ)
  let Z := fun X : Path d => recordIndexPosition ℓ H (fun j => X j-x)
  have hZ : Measurable Z := (measurable_recordIndexPosition ℓ H).comp (by fun_prop)
  rw [successQuenchedKernel_apply _ _ _ _ _ (measurableSet_medianTubeEndpoint ν ℓ hp f x H B R),
    curveIncrement_eq_success_map e f x b B hH ω,Measure.map_apply hZ (Set.to_countable _).measurableSet,
    Measure.restrict_apply (hZ (Set.to_countable _).measurableSet)]
  congr 2
  ext X
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_preimage,
    medianTubeEndpoint,heightTubeEndpointEvent,medianDeviation_le_iff]
  tauto

lemma curveGaussian_failure_le {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (hp : annealedLaw ν (NoDrop (realPosition (step e)) 0) ≠ 0)
    {H : ℕ} (hH : 0 < H) (B R : ℝ) {α c : ℝ} (hα : 0 < α) (hαc : α ≤ c) :
    (environmentLaw ν).real {ω | ¬ ENNReal.ofReal α*crossingQuenched (realPosition (step e)) 0 H ω ≤
      curveIncrement (realPosition (step e)) f 0
        (fun j => (recordMedian ν (realPosition (step e)) hp f j:ℝ)) B H ω
        {u | |signedCoordinate f u-(recordMedian ν (realPosition (step e)) hp f H:ℝ)| ≤ R}} ≤
    (environmentLaw ν).real {ω | (successQuenchedKernel (realPosition (step e)) 0 H ω).real
      (medianTubeEndpoint ν (realPosition (step e)) hp f 0 H B R) < c} := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [crossingQuenched_positive_ae ν hue (realPosition (step e)) (signed_direction_unit e) htrans]
    with ω hω
  intro hbad
  have hh : successQuenchedKernel (realPosition (step e)) 0 H ω
      (medianTubeEndpoint ν (realPosition (step e)) hp f 0 H B R) < ENNReal.ofReal α := by
    rw [success_medianTube_curveIncrement ν e f hp 0 hH B R ω]
    apply lt_of_not_ge
    intro hh
    have hh := (ENNReal.mul_le_iff_le_inv (hω 0 H) (measure_ne_top _ _)).mpr hh
    exact hbad (by simpa only [mul_comm] using hh)
  have hh' := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hh
  rw [ENNReal.toReal_ofReal hα.le] at hh'
  exact hh'.trans_le hαc
end DirectionalTransience

end

end

end OAI
