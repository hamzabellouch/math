import Mathlib
import OAI.Probability.Ballisticity.Stationary.ArrayProfileConsistency
import OAI.Probability.Ballisticity.Estimates.SurvivalLimit
import OAI.Probability.Ballisticity.Stationary.ArrayPermutation
import OAI.Probability.Ballisticity.Estimates.Dust

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def arrayDust {d : ℕ} (e : Direction d) (i : ℤ) (a : ℕ) (Y : ActualEpisodeArray e) : Prop :=
  (Y.2.2.1 (i,(i,a),0):ℝ)=0

lemma arrayDust_measurable {d : ℕ} (e : Direction d) (i : ℤ) (a : ℕ) :
    MeasurableSet {Y : ActualEpisodeArray e | arrayDust e i a Y} := by
  exact (show Measurable (fun Y : ActualEpisodeArray e => (Y.2.2.1 (i,(i,a),0):ℝ)) from by fun_prop)
    (measurableSet_singleton 0)

noncomputable def arrayDustFrequency {d : ℕ} (e : Direction d) (i : ℤ) (n : ℕ)
    (Y : ActualEpisodeArray e) : ℝ := ReferenceClasses.dustFrequency (fun a => arrayDust e i a Y) n

lemma currentDust_array {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ) (Y : ActualEpisodeArray e) (a : ℕ) :
    currentDust e (typedCurrentArrayWindow e i m Y).1 a ↔ arrayDust e i a Y := Iff.rfl

lemma currentDustFrequency_array {d : ℕ} (e : Direction d) (i : ℤ) (m n : ℕ) (Y : ActualEpisodeArray e) :
    currentDustFrequency e n (typedCurrentArrayWindow e i m Y).1 = arrayDustFrequency e i n Y := rfl

lemma arrayDustFrequency_nonneg {d : ℕ} (e : Direction d) (i : ℤ) (n : ℕ) (Y : ActualEpisodeArray e) :
    0≤arrayDustFrequency e i n Y := by
  unfold arrayDustFrequency ReferenceClasses.dustFrequency
  positivity

lemma arrayDust_current_isolated {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ) (Y : ActualEpisodeArray e)
    (hO : ArrayOffsetsConsistent e Y) (hP : ArrayProfilesConsistent e Y)
    (hzero : ∀ p q z, p≠q → arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0) :
    ∀ a, currentDust e (typedCurrentArrayWindow e i m Y).1 a → ∀ b,
      ReferenceClasses.related (typedCurrentArrayWindow e i m Y).1.1 a b → a=b := by
  intro a ha b hr
  by_contra hab
  obtain ⟨z,hz⟩ := hr
  have ho : ReferenceClasses.Consistent (currentOffsets e i Y) := hO (fun a => (i,a))
  have hz' : Y.2.1 ((i,a),(i,b))=(z:OnePoint (HorizontalSpace e)) := by
    simpa only [typedCurrentArrayWindow,dite_eq_left ho,currentOffsets] using hz
  exact dust_isolated e Y hO hP hzero (i,a) (i,b) (by simpa using hab) ha z hz'

lemma arraySurvivalAverage_le_one {d : ℕ} (e : Direction d) (i : ℤ) (m H n : ℕ)
    (hn : 0<n) (Y : ActualEpisodeArray e) : arraySurvivalAverage e i m H n Y≤1 := by
  have hk (a : ℕ) : upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ≠⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (upperHorizontalKernel_mass_le_one e H _ 0)
  rw [arraySurvivalAverage,arraySurvivalSum,ENNReal.toReal_sum (fun a _ => hk a)]
  calc
    _ ≤ (n:ℝ)⁻¹*∑ _a∈Finset.range n, (1:ℝ) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun a _ => by
        simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
          (upperHorizontalKernel_mass_le_one e H (arrayUpperRows e i m a Y) 0)) (by positivity)
    _ = 1 := by simp [hn.ne']

lemma arrayDustWeight_le_survival {d : ℕ} (e : Direction d) (i : ℤ) (m H n : ℕ)
    (Y : ActualEpisodeArray e)
    (h : ∀ a, upperNoDrop e (arrayUpperRows e i m a Y)≤
      upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ) :
    currentDustWeight e n (typedCurrentArrayWindow e i m Y)≤arraySurvivalAverage e i m H n Y := by
  have hk (a : ℕ) : upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ≠⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (upperHorizontalKernel_mass_le_one e H _ 0)
  rw [arraySurvivalAverage,arraySurvivalSum,ENNReal.toReal_sum (fun a _ => hk a)]
  unfold currentDustWeight ReferenceClasses.dustWeight sampleAverage
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro a _
  dsimp only
  split_ifs
  · exact ENNReal.toReal_mono (hk a) (h a)
  · exact ENNReal.toReal_nonneg

lemma array_dust_reference_facts {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (μ : Measure (ActualEpisodeArray e)) [IsProbabilityMeasure μ]
    (hconsistent : ∀ᵐ Y ∂μ, ArrayOffsetsConsistent e Y ∧ ArrayProfilesConsistent e Y)
    (hzero : ∀ᵐ Y ∂μ, ∀ p q z, p≠q → arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0)
    (hentropy : ∀ i m, let W:=μ.map (typedCurrentArrayWindow e i m)
      klDiv W (W.fst.compProd (currentWindowReference e ν))≠⊤) :
    ∀ᵐ Y ∂μ, ∀ (i : ℤ) (m : ℕ),
      Tendsto (fun r : ℕ => currentDustWeight e (2^r) (typedCurrentArrayWindow e i m Y)-
        upperNoDropMean e ν*arrayDustFrequency e i (2^r) Y) atTop (𝓝 0) ∧
      ∀ a H : ℕ, upperNoDrop e (arrayUpperRows e i m a Y)≤
        upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro m
  let F := typedCurrentArrayWindow e i m
  let W := μ.map F
  have hm : Measurable F := typedCurrentArrayWindow_measurable e i m
  have : IsProbabilityMeasure W := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have hi : ∀ᵐ A ∂W.fst, ∀ a, currentDust e A a → ∀ b, ReferenceClasses.related A.1 a b → a=b := by
    change ∀ᵐ A ∂(μ.map F).map Prod.fst, _
    rw [Measure.map_map measurable_fst hm]
    apply (ae_map_iff ((measurable_fst.comp hm).aemeasurable) _).mpr
    · filter_upwards [hconsistent,hzero] with Y hY hz
      exact arrayDust_current_isolated e i m Y hY.1 hY.2 hz
    · simp only [Set.ofPred_forall]
      refine MeasurableSet.iInter fun a => (currentDust_measurable e a).imp ?_
      simp only [Set.ofPred_forall]
      refine MeasurableSet.iInter fun b => ((ReferenceClasses.measurable_related a b).preimage measurable_fst).imp ?_
      by_cases hab : a=b <;> simp [hab]
  have hc := current_reference_dust_law e ν W hi (hentropy i m)
  have hq := current_reference_nodrop_le e ν htrans W (hentropy i m)
  have hv := ae_of_ae_map hm.aemeasurable (hc.and hq)
  exact hv

lemma array_dust_frequency_zero {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (Y : ActualEpisodeArray e) (i : ℤ)
    (href : ∀ m, Tendsto (fun r : ℕ => currentDustWeight e (2^r) (typedCurrentArrayWindow e i m Y)-
      upperNoDropMean e ν*arrayDustFrequency e i (2^r) Y) atTop (𝓝 0) ∧
      ∀ a H : ℕ, upperNoDrop e (arrayUpperRows e i m a Y)≤
        upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ)
    (hmarks : ∀ j, (Y.1 j).1<⊤) (hsurv : ArrayAveragedSurvival e Y)
    (hcost : ∀ ε : ℝ, 0<ε → ∃ m, (expNeg (arrayWindowCost e i m Y)).toReal<ε) :
    Tendsto (fun r : ℕ => arrayDustFrequency e i (2^r) Y) atTop (𝓝 0) := by
  have hfin (m : ℕ) : arrayWindowHeight e i m Y≠⊤ := by
    unfold arrayWindowHeight
    exact (ENat.sum_ne_top).mpr fun j hj => (hmarks (i+j)).ne
  let H := fun m => (arrayWindowHeight e i m Y).toNat
  have hH (m : ℕ) : arrayWindowHeight e i m Y=(H m:ℕ∞) := (ENat.natCast_toNat (hfin m)).symm
  apply average_zero_of_survival (upperNoDropMean e ν) (upperNoDropMean_pos e ν hue htrans)
    _ (fun r => arrayDustFrequency_nonneg e i _ Y)
    (fun m r => arraySurvivalAverage e i m (H m) (2^r) Y)
    (fun m r => currentDustWeight e (2^r) (typedCurrentArrayWindow e i m Y))
    (fun m => (expNeg (arrayWindowCost e i m Y)).toReal)
  · intro m
    exact isBoundedUnder_of_eventually_le (Eventually.of_forall fun r => arraySurvivalAverage_le_one e i m (H m) (2^r) (by positivity) Y)
  · exact fun m r => arrayDustWeight_le_survival e i m (H m) _ Y (fun a => (href m).2 a (H m))
  · exact fun m => (href m).1
  · exact fun m => hsurv i m (H m) (hH m)
  · exact hcost

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma arrayDust_perm {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ) (i : ℤ) (a : ℕ)
    (Y : ActualEpisodeArray e) : arrayDust e i a (arrayPerm e σ Y) ↔ arrayDust e i (σ a) Y := Iff.rfl

lemma array_no_dust_on_frequency_zero {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    [IsProbabilityMeasure μ] (i : ℤ) (E : Set (ActualEpisodeArray e)) (hE : MeasurableSet E)
    (hperm : ∀ σ, MeasurePreserving (arrayPerm e σ) μ μ)
    (hEinv : ∀ σ, ∀ᵐ Y ∂μ, arrayPerm e σ Y∈E ↔ Y∈E)
    (hfreq : ∀ᵐ Y ∂μ, Y∈E → Tendsto (fun r : ℕ => arrayDustFrequency e i (2^r) Y) atTop (𝓝 0)) :
    ∀ᵐ Y ∂μ, Y∈E → ∀ a, ¬arrayDust e i a Y := by
  let I : ℕ → ActualEpisodeArray e → ℝ := fun a Y => if Y∈E ∧ arrayDust e i a Y then 1 else 0
  have hm (a : ℕ) : Measurable (I a) := Measurable.ite (hE.inter (arrayDust_measurable e i a)) measurable_const measurable_const
  have hb (a : ℕ) (Y : ActualEpisodeArray e) : I a Y∈Set.Icc 0 1 := by dsimp [I]; split_ifs <;> norm_num
  have hmean (a : ℕ) : (∫ Y, I a Y ∂μ)=∫ Y, I 0 Y ∂μ := by
    let σ := Equiv.swap 0 a
    have he : (fun Y => I 0 (arrayPerm e σ Y))=ᵐ[μ] I a := by
      filter_upwards [hEinv σ] with Y hY
      dsimp only [I]
      rw [hY,arrayDust_perm,Equiv.swap_apply_left]
    calc
      _ = ∫ Y, I 0 (arrayPerm e σ Y) ∂μ := (integral_congr_ae he).symm
      _ = ∫ Y, I 0 Y ∂μ := by
        rw [←integral_map (hperm σ).measurable.aemeasurable (hm 0).aestronglyMeasurable,(hperm σ).map_eq]
  have hav : ∀ᵐ Y ∂μ, Tendsto (fun r : ℕ => ((2^r:ℕ):ℝ)⁻¹*∑ a∈Finset.range (2^r), I a Y) atTop (𝓝 0) := by
    filter_upwards [hfreq] with Y hY
    by_cases hy : Y∈E
    · simpa only [I,hy,true_and,arrayDustFrequency,ReferenceClasses.dustFrequency] using hY hy
    · simp only [I,hy,false_and,ite_false,Finset.sum_const_zero,mul_zero]
      exact tendsto_const_nhds
  have hz := symmetric_indicator_zero_of_average μ I hm hb hmean (fun r => 2^r) (fun r => by positivity) hav
  filter_upwards [hz] with Y hY hy a ha
  have hh := hY a
  simp only [I,hy,ha,and_self,ite_true] at hh
  norm_num at hh

lemma array_no_dust_on_cost_decay {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (μ : Measure (ActualEpisodeArray e)) [IsProbabilityMeasure μ]
    (hconsistent : ∀ᵐ Y ∂μ, ArrayOffsetsConsistent e Y ∧ ArrayProfilesConsistent e Y)
    (hzero : ∀ᵐ Y ∂μ, ∀ p q z, p≠q → arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0)
    (hentropy : ∀ i m, let W:=μ.map (typedCurrentArrayWindow e i m)
      InformationTheory.klDiv W (W.fst.compProd (currentWindowReference e ν))≠⊤)
    (hmarks : ∀ᵐ Y ∂μ, ∀ j, (Y.1 j).1<⊤)
    (hsurv : ∀ᵐ Y ∂μ, ArrayAveragedSurvival e Y)
    (hperm : ∀ σ, MeasurePreserving (arrayPerm e σ) μ μ)
    (i : ℤ) (E : Set (ActualEpisodeArray e)) (hE : MeasurableSet E)
    (hEinv : ∀ σ, ∀ᵐ Y ∂μ, arrayPerm e σ Y∈E ↔ Y∈E)
    (hcost : ∀ᵐ Y ∂μ, Y∈E → ∀ ε : ℝ, 0<ε → ∃ m, (expNeg (arrayWindowCost e i m Y)).toReal<ε) :
    ∀ᵐ Y ∂μ, Y∈E → ∀ a, ¬arrayDust e i a Y := by
  apply array_no_dust_on_frequency_zero e μ i E hE hperm hEinv
  have href := array_dust_reference_facts e ν htrans μ hconsistent hzero hentropy
  filter_upwards [href,hmarks,hsurv,hcost] with Y hr hm hs hc hY
  exact array_dust_frequency_zero e ν hue htrans Y i (hr i) hm hs (hc hY)

end DirectionalTransience

end

end OAI
