import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkMarkedTangentLimit
import OAI.Probability.Perceptron.Variational.ProbabilityMaps
import OAI.Probability.Perceptron.Variational.RoundedLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def timeGridRound (n : ℕ) (r : Time) : Time :=
  roundTime (unitQuantileField id monotone_id) n r

lemma timeGridRound_tendsto (r : Time) :
    Tendsto (fun n => timeGridRound n r) atTop (𝓝 r) :=
  roundTime_tendsto id monotone_id r

lemma roundedTimeValue_code_ae (q : Time → Time) (hq : Monotone q) (n : ℕ) :
    ∀ᵐ r ∂timeLaw.map q,
      roundTimeValue (unitQuantileField q hq) n (roundedLevelCode (unitQuantileField q hq) n r) =
        timeGridRound n r := by
  apply (ae_map_iff hq.measurable.aemeasurable (by
    apply measurableSet_eq_fun
    · exact (measurable_of_countable (roundTimeValue (unitQuantileField q hq) n)).comp
        (roundedLevelCode_measurable (unitQuantileField q hq) n)
    · exact (show Measurable (fun r : Time => roundLower n (r : ℝ)) from
        (roundLower_measurable n).comp measurable_subtype_coe).subtype_mk)).mpr
  filter_upwards [orderedRoundCode_label (unitQuantileField q hq) n,
    (strictRoundModel (unitQuantileField q hq) n).agrees] with u hu hv
  apply Subtype.ext
  change (strictRoundModel (unitQuantileField q hq) n).value
    (orderedLevelCode (strictRoundModel (unitQuantileField q hq) n).value (roundLower n (q u))) = _
  change orderedLevelCode _ (roundLower n (q u : ℝ)) = _ at hu
  rw [hu]
  exact hv

lemma roundedTimeValue_code_array_ae
    (μ : ProbabilityMeasure (CompactArray Time)) (q : Time → Time) (hq : Monotone q)
    (hpair : (μ : Measure (CompactArray Time)).map (fun Q => Q 0 1) = timeLaw.map q)
    (hsy : ∀ᵐ Q ∂(μ : Measure (CompactArray Time)), ∀ i j, Q i j = Q j i)
    (he : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=Time) e)
      (μ : Measure _) (μ : Measure _)) :
    ∀ᵐ Q ∂(μ : Measure (CompactArray Time)), ∀ n i j, i ≠ j →
      roundTimeValue (unitQuantileField q hq) n (roundedLevelCode (unitQuantileField q hq) n (Q i j)) =
        timeGridRound n (Q i j) := by
  apply ae_all_iff.mpr
  intro n
  have hp := roundedTimeValue_code_ae q hq n
  rw [←hpair] at hp
  have hp' := ae_of_ae_map (show Measurable (fun Q : CompactArray Time => Q 0 1) from by fun_prop).aemeasurable hp
  apply compact_exchangeable_offdiag_ae μ he (fun r =>
    roundTimeValue (unitQuantileField q hq) n (roundedLevelCode (unitQuantileField q hq) n r) =
      timeGridRound n r)
  filter_upwards [hp',hsy] with Q hQ hs
  simpa only [hs 1 0] using hQ

def timeMarkedDecode {K : Type*} (P : Time → K) (D : K) (Q : CompactArray Time) : CompactArray K :=
  fun i j => if i = j then D else P (Q i j)

lemma timeMarkedDecode_measurable {K : Type*} [MeasurableSpace K]
    {P : Time → K} (hP : Measurable P) (D : K) : Measurable (timeMarkedDecode P D) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  unfold timeMarkedDecode
  split_ifs
  · exact measurable_const
  · exact hP.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))

theorem cavityLabelMarkedLaw_tendsto_graph
    (μ : ProbabilityMeasure (CompactArray Time)) (q : Time → Time) (hq : Monotone q)
    (hpair : (μ : Measure (CompactArray Time)).map (fun Q => Q 0 1) = timeLaw.map q)
    (hGG : ∀ n (i : Fin n) (F : CompactBlock Time n →ᵇ ℝ) (g : Time →ᵇ ℝ),
      compactGGDefect μ n i F g = 0)
    (hgeo : ∀ᵐ Q ∂(μ : Measure (CompactArray Time)),
      (∀ i j, Q i j = Q j i) ∧ (∀ i, Q i i = 1) ∧
      ∀ i j l, min (Q i j) (Q i l) ≤ Q j l)
    (he : ∀ e : Equiv.Perm ℕ, MeasurePreserving (compactRelabel (K:=Time) e)
      (μ : Measure _) (μ : Measure _))
    {K : ℝ} (P : Time → BulkPairRange K) (hP : Continuous P) (D : BulkPairRange K) :
    Tendsto (fun n => cavityLabelMarkedLaw
      (fun i => P (roundTimeValue (unitQuantileField q hq) n i)) D
      (stepCumulative (strictRoundModel (unitQuantileField q hq) n).weight)) atTop
      (𝓝 (μ.map (timeMarkedDecode P D))) := by
  let f := unitQuantileField q hq
  let F n := depthMarkedDecode (fun i => P (roundTimeValue f n i)) D ∘ finiteCodeArray (roundedLevelCode f n)
  let G := timeMarkedDecode P D
  have hF n : Measurable (F n) :=
    (depthMarkedDecode_measurable _ _).comp (finiteCodeArray_measurable (roundedLevelCode_measurable f n))
  have hG : Measurable G := timeMarkedDecode_measurable hP.measurable D
  have ht : ∀ᵐ Q ∂(μ : Measure (CompactArray Time)), Tendsto (fun n => F n Q) atTop (𝓝 (G Q)) := by
    filter_upwards [roundedTimeValue_code_array_ae μ q hq hpair (hgeo.mono fun _ h => h.1) he] with Q hQ
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · simpa only [F,G,Function.comp_def,depthMarkedDecode,timeMarkedDecode,ite_eq_left hij] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => D) atTop (𝓝 D))
    · have h := hP.continuousAt.tendsto.comp (timeGridRound_tendsto (Q i j))
      convert h using 1
      · funext n
        dsimp only [F,G,Function.comp_def,depthMarkedDecode,timeMarkedDecode,finiteCodeArray]
        rw [ite_eq_right hij,hQ n i j hij]
      · simp only [G,timeMarkedDecode,ite_eq_right hij]
  have hlim := probabilityMap_tendsto_of_ae_tendsto μ F G hF hG ht
  have hl n : cavityLabelMarkedLaw (fun i => P (roundTimeValue f n i)) D
      (stepCumulative (strictRoundModel f n).weight) = μ.map (F n) := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [cavityLabelMarkedLaw_eq_depth,indexedDepthLaw_eq_rounded_bulk μ q hq hpair hGG hgeo n,
      Measure.map_map (depthMarkedDecode_measurable _ _) (finiteCodeArray_measurable (roundedLevelCode_measurable f n))]
    rfl
  change Tendsto (fun n => cavityLabelMarkedLaw (fun i => P (roundTimeValue f n i)) D
    (stepCumulative (strictRoundModel f n).weight)) atTop (𝓝 (μ.map G))
  simpa only [hl] using hlim

end SphericalPerceptronFreeEnergy

end

end OAI
