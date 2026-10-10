import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ConditionalRMS
import OAI.Analysis.CoulombRadii.Packets.AnnularAddback

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

namespace RecordedEnsemble
variable {n : ℕ}

lemma Conserves.positive_addback_RMS {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) (W V A : Configuration n → ℝ)
    (hW : Measurable W) (hV : Measurable V) (hA : Measurable A)
    {BW BV BA : ℝ} (hBW : 0≤ BW) (hBV : 0≤ BV) (hBA : 0≤ BA)
    (hwb : ∀ x, |W x|≤ BW) (hvb : ∀ x, |V x|≤ BV) (hab : ∀ x, |A x|≤ BA)
    (ha0 : ∀ x, 0≤ A x) (hwa : ∀ x, W x≤ V x+A x) :
    T.dataRMS (fun p s x => max (coreConditionalObservable (T.vector p)
      (W ∘ reindexConfiguration (T.labels p)) s x) 0) ≤
      2*(T.dataRMS (fun p s x => max (coreConditionalObservable (T.vector p)
        (V ∘ reindexConfiguration (T.labels p)) s x) 0)+rawRMS ψ A) := by
  let F p := coreConditionalObservable (T.vector p) (W ∘ reindexConfiguration (T.labels p))
  let G p := coreConditionalObservable (T.vector p) (V ∘ reindexConfiguration (T.labels p))
  let H p := coreConditionalObservable (T.vector p) (A ∘ reindexConfiguration (T.labels p))
  have hsum (x) : |V x+A x|≤ BV+BA := (abs_add_le _ _).trans (add_le_add (hvb x) (hab x))
  have hh p s x : 0≤ H p s x := coreConditionalObservable_nonneg _ _ (fun _ => ha0 _) s x
  have hfg p s x : max (F p s x) 0≤ max (G p s x) 0+H p s x := by
    have he := coreConditionalObservable_add (T.vector p)
      (V ∘ reindexConfiguration (T.labels p)) (A ∘ reindexConfiguration (T.labels p))
      (hV.comp (reindexConfiguration_continuous (T.labels p)).measurable)
      (hA.comp (reindexConfiguration_continuous (T.labels p)).measurable) (fun _ => hvb _) (fun _ => hab _) s x
    have hm := coreConditionalObservable_mono (T.vector p)
      (W ∘ reindexConfiguration (T.labels p)) (fun x => (V ∘ reindexConfiguration (T.labels p)) x+(A ∘ reindexConfiguration (T.labels p)) x)
      (hW.comp (reindexConfiguration_continuous (T.labels p)).measurable)
      ((hV.add hA).comp (reindexConfiguration_continuous (T.labels p)).measurable)
      (fun _ => hwb _) (fun _ => hsum _) (fun _ => hwa _) s x
    rw [he] at hm
    exact max_le (hm.trans (add_le_add (le_max_left _ _) le_rfl))
      (add_nonneg (le_max_right _ _) (hh p s x))
  have hiG p s := coreConditionalObservable_positive_weight_integrable (T.vector p)
    (V ∘ reindexConfiguration (T.labels p))
    (hV.comp (reindexConfiguration_continuous (T.labels p)).measurable) hBV (fun _ => hvb _) s 2
  have hiH p s := coreConditionalObservable_square_weight_integrable (T.vector p)
    (A ∘ reindexConfiguration (T.labels p))
    (hA.comp (reindexConfiguration_continuous (T.labels p)).measurable) hBA (fun _ => hab _) s
  have hsq : (T.dataRMS (fun p s x => max (F p s x) 0))^2 ≤
      2*(T.dataRMS (fun p s x => max (G p s x) 0))^2+2*(T.dataRMS H)^2 := by
    simp only [dataRMS_sq,sliceExpectation]
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s hs
    rw [←integral_const_mul,←integral_const_mul,←integral_add ((hiG p s).const_mul 2) ((hiH p s).const_mul 2)]
    apply integral_mono_ae
    · exact coreConditionalObservable_positive_weight_integrable (T.vector p)
        (W ∘ reindexConfiguration (T.labels p))
        (hW.comp (reindexConfiguration_continuous (T.labels p)).measurable) hBW (fun _ => hwb _) s 2
    · exact ((hiG p s).const_mul 2).add ((hiH p s).const_mul 2)
    · filter_upwards [] with x
      have Hsq : (max (F p s x) 0)^2≤2*(max (G p s x) 0)^2+2*(H p s x)^2 := by
        have H1 := pow_le_pow_left₀ (le_max_right (F p s x) 0) (hfg p s x) 2
        nlinarith [sq_nonneg (max (G p s x) 0-H p s x)]
      have H2 := mul_le_mul_of_nonneg_left Hsq (mass_nonneg ((T.vector p).coreSlice s x))
      nlinarith
  have hH := hT.dataRMS_conditional_le A hA hBA hab
  have hmG := T.dataRMS_nonneg (fun p s x => max (G p s x) 0)
  have hmH := T.dataRMS_nonneg H
  have hR := rawRMS_nonneg ψ A
  change T.dataRMS (fun p s x => max (F p s x) 0) ≤
    2*(T.dataRMS (fun p s x => max (G p s x) 0)+rawRMS ψ A)
  change T.dataRMS H ≤ rawRMS ψ A at hH
  nlinarith [T.dataRMS_nonneg (fun p s x => max (F p s x) 0)]

def innerSquare {J : ℕ} (T : RecordedEnsemble n) (S : Nuclei J) (h : ℝ) (y : Space) : ℝ :=
  ∑ p, sliceExpectation (T.vector p) (fun s x =>
    (max (coreConditionalObservable (T.vector p)
      (rawSignedField (attraction S y) (Metric.ball 0 h) y) s x) 0)^2)
lemma innerSquare_nonneg {J : ℕ} (T : RecordedEnsemble n) (S : Nuclei J) (h : ℝ) (y : Space) :
    0≤ T.innerSquare S h y := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      integral_nonneg (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _))))

lemma Conserves.innerSquare_addback {J : ℕ} {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) (S : Nuclei J) {u h : ℝ} (hu : 0<u) (hh : h≤ u/4)
    {y : Space} (hylo : u/2≤‖y‖) (hyhi : ‖y‖≤4*u) :
    Real.sqrt (T.innerSquare S h y) ≤2*(Real.sqrt (T.rawSquare S y (atomicCellScale y))+
      rawRMS ψ (arrayStatistic (annularAddbackKernel h u))) := by
  have ha : 0<40*atomicCellScale y := by unfold atomicCellScale; linarith
  have hA : MeasurableSet {z : Space | 40*atomicCellScale y≤‖z-y‖} :=
    (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hb0 : 0≤|attraction S y|+(n:ℝ)/(40*atomicCellScale y) := by positivity
  have hb1 (x : Configuration n) : |arrayStatistic (annularAddbackKernel h u) x| ≤ (n:ℝ)*(5001/u) := by
    unfold arrayStatistic
    rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => annularAddbackKernel_nonneg hu h _))]
    calc
      _ ≤ ∑ _i : Fin n, 5001/u := Finset.sum_le_sum (fun _ _ => annularAddbackKernel_bound hu h _)
      _ = _ := by simp
  have hb := rawSignedField_abs_le (n:=n) (attraction S y) _ y ha (fun _ hz => innerBall_subset_far hu hh hylo hz)
  have hj := rawSignedField_abs_le (n:=n) (attraction S y) _ y ha (fun _ hz => hz)
  have H := hT.positive_addback_RMS
    (rawSignedField (attraction S y) (Metric.ball 0 h) y)
    (rawSignedField (attraction S y) {z : Space | 40*atomicCellScale y≤‖z-y‖} y)
    (arrayStatistic (annularAddbackKernel h u))
    (rawSignedField_measurable _ measurableSet_ball y) (rawSignedField_measurable _ hA y)
    (arrayStatistic_measurable (annularAddbackKernel_measurable h u)) hb0 hb0 (by positivity)
    hb hj hb1 (fun _ => Finset.sum_nonneg (fun _ _ => annularAddbackKernel_nonneg hu h _))
    (rawInnerField_addback hu hh _ hylo hyhi)
  simpa only [dataRMS,innerSquare,rawSquare,Function.comp_def,rawSignedField_reindex] using H

end RecordedEnsemble
end Coulomb
end

end

end OAI
