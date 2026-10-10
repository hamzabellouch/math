import Mathlib
import OAI.Probability.Ballisticity.Estimates.CurvePolicyLateral

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma jointTubeMass_le_curveIncrement {d : ℕ} (e f : Direction d) (b : ℕ → ℝ)
    {H : ℕ} (hH : 0 < H) (B : ℝ) (x : Lattice d) (ω : Environment d) :
    jointTubeMass (realPosition (step e)) f b H B (Measure.dirac x) ω ≤
      curveIncrement (realPosition (step e)) f x b B H ω Set.univ := by
  rw [jointTubeMass,lintegral_dirac' _ (measurable_of_countable _),curveIncrement_total]
  apply measure_mono_ae
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  rintro ⟨hHit,hmedian,_⟩
  apply (curvePrefix_iff e f x b B hH X h0 hnn).mpr
  refine ⟨hHit,?_⟩
  intro j hj
  by_contra! h
  exact hmedian ⟨j,hj,h⟩

lemma curveIncrement_short_block {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {v : ℝ} (hv : 0 < v) :
    ∃ C : ℝ, 0 < C ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ R : ℝ, 0 < R ∧
      ∀ r : ℝ, R ≤ r → ∀ H : ℕ, 0 < H →
        (H:ℝ) ≤ t*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) r →
      let ℓ := realPosition (step e)
      let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
      (environmentLaw ν).real {ω | curveIncrement ℓ f 0
        (fun j => (recordMedian ν ℓ hp f j:ℝ)) (v*r) H ω Set.univ < ENNReal.ofReal δ} ≤ C*t^2 := by
  obtain ⟨C,hC,t₀,ht₀,hs⟩ := short_block_survival ν hue e f hef htrans hv
  refine ⟨C,hC,t₀,ht₀,?_⟩
  intro t ht htt
  obtain ⟨δ,hδ,R,hR,hs⟩ := hs t ht htt
  refine ⟨min δ 1,lt_min hδ zero_lt_one,min_le_right _ _,R,hR,?_⟩
  intro r hr H hH hh
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let b := fun j => (recordMedian ν ℓ hp f j:ℝ)
  have hs := hs r hr H hH hh 0 (Measure.dirac 0) inferInstance (by simp [signedHeight])
  apply le_trans ?_ hs
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro ω hω
  have hc : (curveIncrement ℓ f 0 b (v*r) H ω Set.univ).toReal < min δ 1 := by
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hω |>.trans_le (by rw [ENNReal.toReal_ofReal (le_min hδ.le zero_le_one)])
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (jointTubeMass_le_curveIncrement e f b hH (v*r) 0 ω)).trans_lt
    (hc.trans_le (min_le_left _ _))
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePolicy_moment {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) {A B ρ : ℝ} (hA : 0 ≤ A) (hAB : A < B) (hρ : 0 ≤ ρ)
    {H : ℕ} (hH : 0 < H) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) (ω : Environment d)
    (ha : crossingQuenched (realPosition (step e)) x H ω ≠ 0) :
    let ℓ := realPosition (step e)
    let E := {u : Lattice d | |signedCoordinate f u-b H| ≤ ρ}
    let W := fun X : Path d => medianDeviation ℓ f b H (fun j => X j-x)
    let μ := (quenchedKernel (ω,x))[|Cross ℓ x H]
    (∫ u, (signedCoordinate f u-b H)^2 ∂curvePolicy ℓ f x b B H E δ α dummy ω) ≤
      ρ^2+(if α*crossingQuenched ℓ x H ω ≤ curveIncrement ℓ f x b B H ω E then 0 else A^2)+
        2*(∫ X, if A < W X then (min (W X) B)^2 else 0 ∂μ) := by
  let ℓ := realPosition (step e)
  let E := {u : Lattice d | |signedCoordinate f u-b H| ≤ ρ}
  let W := fun X : Path d => medianDeviation ℓ f b H (fun j => X j-x)
  let Z := fun X : Path d => recordIndexPosition ℓ H (fun j => X j-x)
  let Y := fun X : Path d => signedCoordinate f (Z X)
  let N := {X | W X ≤ B}
  let μ := (quenchedKernel (ω,x))[|Cross ℓ x H]
  have hZ : Measurable Z := (measurable_recordIndexPosition ℓ H).comp (by fun_prop)
  have hW : Measurable W := (measurable_medianDeviation ℓ f b H).comp (by fun_prop)
  have hY : Measurable Y := (measurable_of_countable (signedCoordinate f)).comp hZ
  have hN : MeasurableSet N := measurableSet_le hW measurable_const
  have hEN : MeasurableSet (N ∩ Z ⁻¹' E) := hN.inter (hZ E.to_countable.measurableSet)
  let : IsProbabilityMeasure μ := cond_isProbabilityMeasure ha
  have hNval : μ N = (crossingQuenched ℓ x H ω)⁻¹ *
      curveIncrement ℓ f x b B H ω Set.univ := by
    rw [curveIncrement_eq_success_map e f x b B hH ω,Measure.map_apply hZ MeasurableSet.univ,
      Set.preimage_univ,Measure.restrict_apply_univ]
    exact cond_apply (measurableSet_cross ℓ x H) _ _
  have hEval : μ (N ∩ Z ⁻¹' E) = (crossingQuenched ℓ x H ω)⁻¹ *
      curveIncrement ℓ f x b B H ω E := by
    rw [curveIncrement_eq_success_map e f x b B hH ω,Measure.map_apply hZ E.to_countable.measurableSet,
      Measure.restrict_apply (hZ E.to_countable.measurableSet)]
    rw [show Z ⁻¹' E ∩ (Cross ℓ x H ∩ N) = Cross ℓ x H ∩ (N ∩ Z ⁻¹' E) by ext X; simp only [Set.mem_inter_iff]; tauto]
    exact cond_apply (measurableSet_cross ℓ x H) _ _
  have htail : 0 ≤ ∫ X, if A < W X then (min (W X) B)^2 else 0 ∂μ :=
    integral_nonneg fun X => by split_ifs <;> positivity
  by_cases hf : curveIncrement ℓ f x b B H ω Set.univ < δ
  · change (∫ u, (signedCoordinate f u-b H)^2 ∂curvePolicy ℓ f x b B H E δ α dummy ω) ≤ _
    simp only [curvePolicy,selectedFiniteKernel,ite_eq_left hf,integral_dirac,hd,sub_self,
      zero_pow (by decide : 2 ≠ 0)]
    split_ifs <;> positivity
  have hNZ : μ N ≠ 0 := by
    rw [hNval]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
      (ne_of_gt (hδ.trans_le (not_lt.mp hf)))
  have hEZ (hs : α*crossingQuenched ℓ x H ω ≤ curveIncrement ℓ f x b B H ω E) :
      μ (N ∩ Z ⁻¹' E) ≠ 0 := by
    rw [hEval]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
      (ne_of_gt ((ENNReal.mul_pos hα.ne' ha).trans_le hs))
  have hh := selectedEndpointLaw_moment μ W Y hW hY (N ∩ Z ⁻¹' E) hEN hA hAB hρ
    (fun X => medianDeviation_nonneg ℓ f b H _) (fun X =>
      (medianDeviation_le_iff ℓ f b H (fun j => X j-x) (W X)).mp le_rfl H le_rfl)
    (curveIncrement ℓ f x b B H ω Set.univ < δ)
    (α*crossingQuenched ℓ x H ω ≤ curveIncrement ℓ f x b B H ω E)
    hNZ hEZ (fun X hX => hX.2)
  rw [← hd] at hh
  rw [← curvePolicy_lateral e f x b B hH E δ α dummy ω] at hh
  rw [integral_map (measurable_of_countable (signedCoordinate f)).aemeasurable (by fun_prop)] at hh
  simpa only [hd] using hh

end DirectionalTransience

end

end

end OAI
