import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.RectifiableCoarea
import OAI.Geometry.CAT0Fillings.Currents.Pushforward
import OAI.Geometry.CAT0Fillings.Prism.Family
import OAI.Geometry.CAT0Fillings.Prism.MixedMass

namespace OAI

section
section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory CurrentOperations MassMeasure
open scoped NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
lemma IntegerChart.cone_controls (C : IntegerChart X k)
    {f : ℝ × X → X} {L R : ℝ≥0} (hf : LipschitzWith L f)
    (ht : ∀ x, LipschitzWith R (fun t : ℝ => f (t,x)))
    (hs : ∀ t, LipschitzWith 1 (fun x : X => f (t,x))) :
    Controls (pushCurrent f C.prism.action)
      (((k+1:ℝ≥0)*R) • ((volume.restrict (Icc (0:ℝ) 1)).prod (currentMassMeasure C.action_isMetricCurrent)).map f) := by
  intro b π hb hπ
  have hab : Admissible b π := ⟨hb,fun i => ⟨1,hπ i⟩⟩
  rw [pushCurrent_apply _ _ hab,integral_smul_nnreal_measure,
    integral_map hf.continuous.aemeasurable hb.continuous.abs.aestronglyMeasurable]
  have h := C.prism_action_bound_mixed (currentMassMeasure_controls C.action_isMetricCurrent)
    (b ∘ f) (fun i => π i ∘ f) (admissible_comp hab hf) R
    (fun i x => by simpa only [one_mul,Function.comp_def] using (hπ i).comp (ht x))
    (fun i t => by simpa only [one_mul,Function.comp_def] using (hπ i).comp (hs t))
  simpa only [NNReal.smul_def,smul_eq_mul,NNReal.coe_mul,NNReal.coe_add,
    NNReal.coe_natCast,NNReal.coe_one,Function.comp_apply] using h

lemma IntegerChart.mass_cone_le (C : IntegerChart X k)
    {f : ℝ × X → X} {L R : ℝ≥0} (hf : LipschitzWith L f)
    (ht : ∀ x, LipschitzWith R (fun t : ℝ => f (t,x)))
    (hs : ∀ t, LipschitzWith 1 (fun x : X => f (t,x))) :
    mass (pushCurrent f C.prism.action) ≤ (k+1:ℝ)*(R:ℝ)*mass C.action := by
  have hh := mass_le_measure inferInstance (C.cone_controls hf ht hs)
  have he : ((((k+1:ℝ≥0)*R) •
      ((volume.restrict (Icc (0:ℝ) 1)).prod (currentMassMeasure C.action_isMetricCurrent)).map f).real univ) =
      (k+1:ℝ)*(R:ℝ)*mass C.action := by
    rw [measureReal_nnreal_smul_apply]
    simp only [Measure.real,Measure.map_apply hf.continuous.measurable MeasurableSet.univ,preimage_univ]
    rw [←Set.univ_prod_univ,Measure.prod_prod,ENNReal.toReal_mul]
    have hv : (volume.restrict (Icc (0:ℝ) 1)) univ = 1 := by simp
    rw [hv,ENNReal.toReal_one,one_mul]
    change (↑((k+1:ℝ≥0)*R):ℝ) * (currentMassMeasure C.action_isMetricCurrent).real univ = _
    rw [currentMassMeasure_total]
    push_cast
    rfl
  exact hh.trans_eq he

lemma mass_prismFamily_cone_le {T : Functional X k} (hT : IsMetricCurrent T)
    (C : ℕ → IntegerChart X k) (hd : Pairwise (fun i j => Disjoint (C i).image (C j).image))
    (hC : ∀ i, IsMetricCurrent (C i).action) (hCS : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π)
    {f : ℝ × X → X} {L R : ℝ≥0} (hf : LipschitzWith L f)
    (ht : ∀ x, LipschitzWith R (fun t : ℝ => f (t,x)))
    (hs : ∀ t, LipschitzWith 1 (fun x : X => f (t,x))) :
    mass (pushCurrent f (prismFamily C)) ≤ (k+1:ℝ)*(R:ℝ)*mass T := by
  let S (i : ℕ) := pushCurrent f (C i).prism.action
  have hS (i) : IsMetricCurrent (S i) := pushCurrent_isMetricCurrent (C i).prism.action_isMetricCurrent hf
  have hM (i) : mass (S i) ≤ ((k+1:ℝ)*(R:ℝ))*mass (C i).action := (C i).mass_cone_le hf ht hs
  have hsum : Summable (fun i => mass (S i)) :=
    (hCS.mul_left ((k+1:ℝ)*(R:ℝ))).of_nonneg_of_le (fun i => mass_nonneg _) hM
  have hp : pushCurrent f (prismFamily C) = (fun b π => ∑' i, S i b π) := by
    funext b π
    by_cases hab : Admissible b π
    · simp only [pushCurrent_apply _ _ hab,prismFamily,S]
    · simp only [pushCurrent,ite_eq_right hab,tsum_zero,S]
  rw [hp]
  calc
    _ ≤ ∑' i, mass (S i) := mass_tsum_le hS hsum
    _ ≤ ∑' i, ((k+1:ℝ)*(R:ℝ))*mass (C i).action := hsum.tsum_le_tsum hM (hCS.mul_left _)
    _ = ((k+1:ℝ)*(R:ℝ))*(∑' i, mass (C i).action) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (chartFamily_mass_sum_le hT C hd hC hCS heq) (by positivity)

end CAT0Fillings

end
end

end OAI
