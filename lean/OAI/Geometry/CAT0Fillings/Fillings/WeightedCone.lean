import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current
import OAI.Geometry.CAT0Fillings.Fillings.Attainment

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma boundarySucc_neg {k : ℕ} (T : Functional X (k+1)) :
    boundarySucc (-T) = -boundarySucc T := by
  funext b π
  by_cases h : Admissible b π <;> simp [boundarySucc,h]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma boundarySucc_add {k : ℕ} (T U : Functional X (k+1)) :
    boundarySucc (T+U) = boundarySucc T+boundarySucc U := by
  funext b π
  by_cases h : Admissible b π <;> simp [boundarySucc,h]

lemma IsIntegral.neg {k : ℕ} {T : Functional X k} (hT : IsIntegral k T) :
    IsIntegral k (-T) := by
  have h0 : IsIntegral k (0 : Functional X k) := isIntegral_zero k
  simpa only [zero_sub] using h0.sub hT

lemma IsIntegral.add {k : ℕ} {T U : Functional X k} (hT : IsIntegral k T)
    (hU : IsIntegral k U) : IsIntegral k (T+U) := by
  simpa only [sub_neg_eq_add] using hT.sub hU.neg

omit [Nonempty X] in
lemma mass_sub_le {k : ℕ} {T U : Functional X k} (hT : IsMetricCurrent T)
    (hU : IsMetricCurrent U) : mass (T-U) ≤ mass T+mass U := by
  simpa only [sub_eq_add_neg,mass_neg] using mass_add_le hT hU.neg

lemma fillingVolume_zero {k : ℕ} : fillingVolume (0 : Functional X (k+1)) = 0 := by
  apply le_antisymm _ (fillingVolume_nonneg _)
  have hb : boundarySucc (0 : Functional X (k+2)) = 0 := by
    funext b π; simp [boundarySucc]
  exact (fillingVolume_le (isIntegral_zero (k+2)) hb).trans_eq (mass_zero (k+2))

lemma fillingVolume_neg (hX : IsCAT0 X) {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) :
    fillingVolume (-T) = fillingVolume T := by
  obtain ⟨S,hS,hb,hm⟩ := hX.exists_minimal_integral_filling hT hz
  have hnz : boundarySucc (-T) = 0 := by rw [boundarySucc_neg,hz,neg_zero]
  obtain ⟨U,hU,hUb,hUm⟩ := hX.exists_minimal_integral_filling hT.neg hnz
  apply le_antisymm
  · exact (fillingVolume_le hS.neg (by rw [boundarySucc_neg,hb])).trans_eq (by rw [mass_neg,hm])
  · exact (fillingVolume_le hU.neg (by rw [boundarySucc_neg,hUb,neg_neg])).trans_eq (by rw [mass_neg,hUm])

lemma fillingVolume_add_le (hX : IsCAT0 X) {k : ℕ} {T U : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hzT : boundarySucc T = 0)
    (hU : IsIntegral (k+1) U) (hzU : boundarySucc U = 0) :
    fillingVolume (T+U) ≤ fillingVolume T+fillingVolume U := by
  obtain ⟨S,hS,hbS,hmS⟩ := hX.exists_minimal_integral_filling hT hzT
  obtain ⟨R,hR,hbR,hmR⟩ := hX.exists_minimal_integral_filling hU hzU
  calc
    _ ≤ mass (S+R) := fillingVolume_le (hS.add hR) (by rw [boundarySucc_add,hbS,hbR])
    _ ≤ mass S+mass R := mass_add_le hS.1 hR.1
    _ = _ := by rw [hmS,hmR]

lemma fillingVolume_sub_le (hX : IsCAT0 X) {k : ℕ} {T U : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hzT : boundarySucc T = 0)
    (hU : IsIntegral (k+1) U) (hzU : boundarySucc U = 0) :
    fillingVolume (T-U) ≤ fillingVolume T+fillingVolume U := by
  have hnz : boundarySucc (-U) = 0 := by rw [boundarySucc_neg,hzU,neg_zero]
  simpa only [←sub_eq_add_neg,fillingVolume_neg hX hU hzU] using
    fillingVolume_add_le hX hT hzT hU.neg hnz

lemma fillingVolume_sub_symm (hX : IsCAT0 X) {k : ℕ} {T U : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hzT : boundarySucc T = 0)
    (hU : IsIntegral (k+1) U) (hzU : boundarySucc U = 0) :
    fillingVolume (T-U) = fillingVolume (U-T) := by
  have hz : boundarySucc (U-T) = 0 := by rw [boundarySucc_sub,hzU,hzT,sub_self]
  simpa only [neg_sub] using fillingVolume_neg hX (hU.sub hT) hz

lemma fillingVolume_triangle (hX : IsCAT0 X) {k : ℕ} {T U V : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hzT : boundarySucc T = 0)
    (hU : IsIntegral (k+1) U) (hzU : boundarySucc U = 0)
    (hV : IsIntegral (k+1) V) (hzV : boundarySucc V = 0) :
    fillingVolume (T-V) ≤ fillingVolume (T-U)+fillingVolume (U-V) := by
  have hh := fillingVolume_add_le hX (hT.sub hU)
    (by rw [boundarySucc_sub,hzT,hzU,sub_self]) (hU.sub hV)
    (by rw [boundarySucc_sub,hzU,hzV,sub_self])
  simpa only [sub_add_sub_cancel] using hh

lemma abs_fillingVolume_sub_le (hX : IsCAT0 X) {k : ℕ} {T U : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hzT : boundarySucc T = 0)
    (hU : IsIntegral (k+1) U) (hzU : boundarySucc U = 0) :
    |fillingVolume T-fillingVolume U| ≤ fillingVolume (T-U) := by
  have hzero : boundarySucc (0 : Functional X (k+1)) = 0 := by
    funext b π; simp [boundarySucc]
  have hi0 : IsIntegral (k+1) (0 : Functional X (k+1)) := isIntegral_zero (k+1)
  have h1 := fillingVolume_triangle hX hT hzT hU hzU hi0 hzero
  have h2 := fillingVolume_triangle hX hU hzU hT hzT hi0 hzero
  simp only [sub_zero,fillingVolume_sub_symm hX hU hzU hT hzT] at h1 h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open MassMeasure CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

namespace ChartGeometry
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma density_nonneg (i : ℕ) (z : Euc k) : 0 ≤ q.density i z :=
  mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

lemma weighted_density_integrable (i : ℕ) {w : X → ℝ} (hw : Continuous w) :
    Integrable (fun z => q.density i z*w ((q.chart i).paramExtended z))
      (volume.restrict (q.chart i).domain) := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hw.continuousOn
  exact (q.density_integrable i).mul_bdd
    (hw.measurable.comp (q.chart i).measurable_paramExtended).aestronglyMeasurable
    (Eventually.of_forall fun z => hB _ (mem_univ _))

lemma integral_massMeasure {w : X → ℝ} (hw : Continuous w) :
    (∫ x, w x ∂currentMassMeasure hT) = ∑' i, ∫ z,
      q.density i z*w ((q.chart i).paramExtended z)
      ∂volume.restrict (q.chart i).domain := by
  have hi := hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace w)
    (μ := currentMassMeasure hT)
  rw [q.measure_eq] at hi ⊢
  rw [integral_sum_measure hi]
  apply tsum_congr
  intro i
  exact integral_densityPush (volume.restrict (q.chart i).domain)
    (q.chart i).measurable_paramExtended (q.density_integrable i)
    (Eventually.of_forall (q.density_nonneg i)) hw

lemma weighted_density_summable {w : X → ℝ} (hw : Continuous w) :
    Summable (fun i => ∫ z, q.density i z*w ((q.chart i).paramExtended z)
      ∂volume.restrict (q.chart i).domain) := by
  have hi := hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace w)
    (μ := currentMassMeasure hT)
  rw [q.measure_eq] at hi
  apply (hasSum_integral_measure hi).summable.congr
  intro i
  exact (integral_densityPush (volume.restrict (q.chart i).domain)
    (q.chart i).measurable_paramExtended (q.density_integrable i)
    (Eventually.of_forall (q.density_nonneg i)) hw)

lemma sweptMass_one_le (o : X) :
    q.sweptMass o (fun _ => 1) ≤ ∫ x, dist o x ∂currentMassMeasure hT := by
  obtain ⟨hI,hIs⟩ := q.swept_integrable_summable o (LipschitzWith.const (1:ℝ)) (fun _ => zero_le_one)
  have hc : Continuous (dist o : X → ℝ) := continuous_const.dist continuous_id
  rw [q.integral_massMeasure hc]
  apply hIs.tsum_le_tsum _ (q.weighted_density_summable hc)
  intro i
  apply integral_mono_ae (hI i) (q.weighted_density_integrable i hc)
  filter_upwards [q.differential i,ae_restrict_mem (q.chart i).borel] with z hp hz
  let α := differentialRow (fderivWithin ℝ ((q.chart i).scalar (dist o)) (q.chart i).domain z)
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hp.2.2 hp.2.1
  have hq : 0 ≤ α ⬝ᵥ (q.gram i z)⁻¹.mulVec α := hG.inv.posSemidef.dotProduct_mulVec_nonneg α
  have hs : Real.sqrt (1-α ⬝ᵥ (q.gram i z)⁻¹.mulVec α) ≤ 1 := by
    apply (Real.sqrt_le_left zero_le_one).mpr
    linarith
  simp only [IntegerChart.sweptWeight,(q.chart i).scalar_eq hz, mul_one,
    IntegerChart.paramExtended,dite_eq_left hz,density,gram]
  calc
    _ ≤ |((q.chart i).multiplicity z : ℝ)| *
        (dist o ((q.chart i).param ⟨z,hz⟩)*1*Real.sqrt (q.gram i z).det) := by
      gcongr
      · simpa only [α,gram] using hs
      · rfl
    _ = _ := by simp only [mul_one,gram]; ring

end ChartGeometry

theorem IsCAT0.exists_integral_filling_weighted (hX : IsCAT0 X)
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) (o : X) :
    ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T ∧
      mass S ≤ ∫ x, dist o x ∂currentMassMeasure hT.1 := by
  obtain ⟨q⟩ := exists_chartGeometry hX hT.1 hT.2.1
  obtain ⟨seg,hends,hseg,hcomp⟩ := hX
  obtain ⟨S,hS,hb,hm⟩ := exists_swept_current hT hz q seg hseg hcomp
    (fun o y => (hends o y).2) o (LipschitzWith.const (1:ℝ))
    (fun _ => zero_le_one) (fun _ => le_refl 1)
  have hp : pushCurrent (fun y => seg o y (1-1)) T = 0 := by
    funext b π
    by_cases hab : Admissible b π
    · rw [pushCurrent_apply _ _ hab]
      simp only [sub_self,show ∀ y, seg o y 0 = o from fun y => (hends o y).1]
      exact hT.1.eq_zero_of_const_coord
        ⟨BoundedLip.const _,fun _ => ⟨0,LipschitzWith.const _⟩⟩ 0 (π 0 o) (fun _ => rfl)
    · simp only [pushCurrent,ite_eq_right hab,Pi.zero_apply]
  refine ⟨-S,hS.neg,?_,?_⟩
  · rw [boundarySucc_neg,hb,hp,zero_sub,neg_neg]
  · rw [mass_neg]
    exact hm.trans (q.sweptMass_one_le o)

omit [Nonempty X] in
lemma IsMetricCurrent.sub {T U : Functional X k} (hT : IsMetricCurrent T)
    (hU : IsMetricCurrent U) : IsMetricCurrent (T-U) := by
  simpa only [sub_eq_add_neg] using hT.add hU.neg

omit [Nonempty X] in
lemma currentMassMeasure_sub_le {T U : Functional X k}
    (hT : IsMetricCurrent T) (hU : IsMetricCurrent U) :
    currentMassMeasure (hT.sub hU) ≤ currentMassMeasure hT+currentMassMeasure hU := by
  apply currentMassMeasure_le
  simpa only [sub_eq_add_neg] using controls_add (currentMassMeasure_controls hT)
    (controls_neg_iff.mpr (currentMassMeasure_controls hU))

omit [Nonempty X] in
lemma integral_dist_massMeasure_sub_le {T U : Functional X k}
    (hT : IsMetricCurrent T) (hU : IsMetricCurrent U) (o : X) :
    (∫ x, dist o x ∂currentMassMeasure (hT.sub hU)) ≤
      (∫ x, dist o x ∂currentMassMeasure hT)+(∫ x, dist o x ∂currentMassMeasure hU) := by
  have hi (μ : Measure X) [IsFiniteMeasure μ] : Integrable (dist o) μ :=
    (continuous_const.dist continuous_id).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact (integral_mono_measure (currentMassMeasure_sub_le hT hU)
    (Eventually.of_forall fun _ => dist_nonneg) (hi _)).trans_eq
    (integral_add_measure (hi _) (hi _))

end CAT0Fillings
end

end OAI
