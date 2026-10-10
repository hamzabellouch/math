import Mathlib
import OAI.Probability.Perceptron.Variational.FieldRounding
import OAI.Probability.Perceptron.Variational.CompactRestorationWitness
import OAI.Probability.Perceptron.Variational.RoundedPairCoefficients

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def unitQuantileField (q : Time→Time) (hq : Monotone q) : BoundedField 1 :=
  ⟨fun u => q u,fun _ _ h => hq h,fun u => (q u).prop.1,fun u => (q u).prop.2⟩

def strictRoundModel {H : ℝ} (q : BoundedField H) (n : ℕ) : FiniteFieldModel (q.round n) :=
  (exists_finiteFieldModel_strict (q.round n) (q.round n).measurable (q.round_finite n)).choose

lemma strictRoundModel_strict {H : ℝ} (q : BoundedField H) (n : ℕ) :
    StrictMono (strictRoundModel q n).value :=
  (exists_finiteFieldModel_strict (q.round n) (q.round n).measurable (q.round_finite n)).choose_spec

def roundTimeValue (q : BoundedField 1) (n : ℕ) : Fin ((strictRoundModel q n).depth+1)→Time :=
  fun i => ⟨(strictRoundModel q n).value i,(strictRoundModel q n).values_mem
    (ae_of_all _ fun u => ⟨(q.round n).nonneg u,(q.round n).le_bound u⟩) i⟩

lemma roundTimeValue_mono (q : BoundedField 1) (n : ℕ) : Monotone (roundTimeValue q n) :=
  (strictRoundModel q n).monotone_value

def roundTime (q : BoundedField 1) (n : ℕ) (u : Time) : Time :=
  ⟨q.round n u,⟨(q.round n).nonneg u,(q.round n).le_bound u⟩⟩

lemma roundTime_mono (q : BoundedField 1) (n : ℕ) : Monotone (roundTime q n) :=
  (q.round n).monotone

lemma BoundedField.round_tendsto {H : ℝ} (q : BoundedField H) (u : Time) :
    Tendsto (fun n => q.round n u) atTop (𝓝 (q u)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  simpa only [Real.dist_eq,Nat.cast_add,Nat.cast_one] using q.round_error n u

lemma roundTime_tendsto (q : Time→Time) (hq : Monotone q) (u : Time) :
    Tendsto (fun n => roundTime (unitQuantileField q hq) n u) atTop (𝓝 (q u)) :=
  tendsto_subtype_rng.mpr ((unitQuantileField q hq).round_tendsto u)

def roundedPairCoeff (q : BoundedField 1) (n : ℕ) (g : Jet3) (v : ℝ→ᵇℝ) :
    Fin ((strictRoundModel q n).depth+1)→ℝ :=
  labelPairCoefficient (strictRoundModel q n).depth (stepCumulative (strictRoundModel q n).weight)
    (strictRoundModel q n).value g
    ⟨1-roundTimeValue q n (Fin.last (strictRoundModel q n).depth),
      sub_nonneg.mpr (roundTimeValue q n _).prop.2⟩ v

lemma roundedPairCoeff_bounds (q : BoundedField 1) (n : ℕ) (g : Jet3) (v : ℝ→ᵇℝ) :
    Monotone (roundedPairCoeff q n g v) ∧
      ∀ i,0≤roundedPairCoeff q n g v i ∧ roundedPairCoeff q n g v i≤‖v‖^2 := by
  have h := labelPairCoefficient_bounds (strictRoundModel q n).depth
    (stepCumulative (strictRoundModel q n).weight)
    (stepCumulative_pos _ (strictRoundModel q n).weight_pos) (strictRoundModel q n).value g
    (⟨1-roundTimeValue q n (Fin.last (strictRoundModel q n).depth),
      sub_nonneg.mpr (roundTimeValue q n _).prop.2⟩ : ℝ≥0) v
  exact ⟨h.2.1,fun i => ⟨h.1 i,(h.2.2.1 i).trans h.2.2.2⟩⟩

def roundedPairFunction (q : BoundedField 1) (n : ℕ) (g : Jet3) (v : ℝ→ᵇℝ) (r : ℝ) : ℝ :=
  finiteMonotoneExtension (strictRoundModel q n).value (roundedPairCoeff q n g v) (roundLower n r)

lemma roundedPairFunction_mono (q : BoundedField 1) (n : ℕ) (g : Jet3) (v : ℝ→ᵇℝ) :
    Monotone (roundedPairFunction q n g v) :=
  (finiteMonotoneExtension_mono _ _ (roundedPairCoeff_bounds q n g v).1).comp (roundLower_monotone n)

lemma roundedPairFunction_bounds (q : BoundedField 1) (n : ℕ) (g : Jet3) (v : ℝ→ᵇℝ) (r : ℝ) :
    0≤roundedPairFunction q n g v r ∧ roundedPairFunction q n g v r≤‖v‖^2 :=
  finiteMonotoneExtension_bounds _ _ _ (fun i => ((roundedPairCoeff_bounds q n g v).2 i).1)
    (fun i => ((roundedPairCoeff_bounds q n g v).2 i).2) _

lemma roundedPairFunction_agrees (q : BoundedField 1) (n : ℕ) (g : Jet3) (v : ℝ→ᵇℝ) :
    (fun u => roundedPairFunction q n g v (q u)) =ᵐ[timeLaw]
      (fun u => roundedPairCoeff q n g v ((strictRoundModel q n).label u)) := by
  filter_upwards [(strictRoundModel q n).agrees] with u hu
  change finiteMonotoneExtension _ _ (roundLower n (q u))=_
  change (strictRoundModel q n).value ((strictRoundModel q n).label u)=roundLower n (q u) at hu
  rw [←hu,finiteMonotoneExtension_value _ _ (strictRoundModel_strict q n) (roundedPairCoeff_bounds q n g v).1]

lemma roundedPair_selection (q : BoundedField 1) (g : Jet3) (v : ℝ→ᵇℝ) :
    ∃ (s : ℕ→ℕ) (a : ℝ→ℝ), StrictMono s ∧ Monotone a ∧
      (∀ r,0≤a r ∧ a r≤‖v‖^2) ∧ ∀ r,
      Tendsto (fun n => roundedPairFunction q (s n) g v r) atTop (𝓝 (a r)) :=
  bounded_monotone_helly _ _ (fun n => roundedPairFunction_mono q n g v)
    (fun n r => roundedPairFunction_bounds q n g v r)

lemma roundedPair_sum_integral (q : BoundedField 1) (n : ℕ) (g : Jet3) (v : ℝ→ᵇℝ)
    (F : CompactOverlap→ᵇℝ) (e : ℕ) :
    (∑ i,(strictRoundModel q n).weight i*F (timeSpin (roundTimeValue q n i))*(roundedPairCoeff q n g v i)^e)=
      ∫ u,F (timeSpin (roundTime q n u))*(roundedPairFunction q n g v (q u))^e ∂timeLaw := by
  have he := integral_finite_label (strictRoundModel q n).label (strictRoundModel q n).measurable_label
    (fun i => F (timeSpin (roundTimeValue q n i))*(roundedPairCoeff q n g v i)^e)
  simp only [←mul_assoc] at he
  simp only [FiniteFieldModel.weight]
  rw [←he]
  apply integral_congr_ae
  filter_upwards [(strictRoundModel q n).agrees,roundedPairFunction_agrees q n g v] with u hu hv
  have ht : roundTimeValue q n ((strictRoundModel q n).label u)=roundTime q n u := Subtype.ext hu
  rw [ht,hv]

lemma roundedPair_sum_tendsto (q : Time→Time) (hq : Monotone q) (g : Jet3) (v : ℝ→ᵇℝ)
    (s : ℕ→ℕ) (hs : StrictMono s) (a : ℝ→ℝ)
    (ha : ∀ r,Tendsto (fun n => roundedPairFunction (unitQuantileField q hq) (s n) g v r)
      atTop (𝓝 (a r))) (F : CompactOverlap→ᵇℝ) (e : ℕ) :
    Tendsto (fun n => ∑ i,(strictRoundModel (unitQuantileField q hq) (s n)).weight i*
      F (timeSpin (roundTimeValue (unitQuantileField q hq) (s n) i))*
        (roundedPairCoeff (unitQuantileField q hq) (s n) g v i)^e) atTop
      (𝓝 (∫ u,F (timeSpin (q u))*(a (q u))^e ∂timeLaw)) := by
  simp_rw [roundedPair_sum_integral]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖*(‖v‖^2)^e)
  · intro n
    exact ((F.measurable.comp (timeSpin_continuous.measurable.comp (roundTime_mono _ _).measurable)).mul
      (((roundedPairFunction_mono _ _ _ _).measurable.comp (unitQuantileField q hq).measurable).pow_const e)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun u => by
      rw [norm_mul,norm_pow]
      apply mul_le_mul (F.norm_coe_le_norm _) _ (by positivity) (norm_nonneg _)
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [Real.norm_eq_abs,abs_of_nonneg (roundedPairFunction_bounds _ _ _ _ _).1]
      exact (roundedPairFunction_bounds _ _ _ _ _).2
  · exact ae_of_all _ fun u =>
      (((F.continuous.comp timeSpin_continuous).tendsto _).comp
        ((roundTime_tendsto q hq u).comp hs.tendsto_atTop)).mul ((ha (q u)).pow e)

lemma roundTime_sum_integral (q : BoundedField 1) (n : ℕ) (F : CompactOverlap→ᵇℝ) :
    (∑ i,(strictRoundModel q n).weight i*F (timeSpin (roundTimeValue q n i)))=
      ∫ u,F (timeSpin (roundTime q n u)) ∂timeLaw := by
  have he := integral_finite_label (strictRoundModel q n).label (strictRoundModel q n).measurable_label
    (fun i => F (timeSpin (roundTimeValue q n i)))
  simp only [FiniteFieldModel.weight]
  rw [←he]
  apply integral_congr_ae
  filter_upwards [(strictRoundModel q n).agrees] with u hu
  exact congrArg (fun t => F (timeSpin t)) (Subtype.ext hu)

lemma roundTime_sum_tendsto (q : Time→Time) (hq : Monotone q) (F : CompactOverlap→ᵇℝ) :
    Tendsto (fun n => ∑ i,(strictRoundModel (unitQuantileField q hq) n).weight i*
      F (timeSpin (roundTimeValue (unitQuantileField q hq) n i))) atTop
      (𝓝 (∫ u,F (timeSpin (q u)) ∂timeLaw)) := by
  simp_rw [roundTime_sum_integral]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact (F.measurable.comp (timeSpin_continuous.measurable.comp (roundTime_mono _ _).measurable)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun u => F.norm_coe_le_norm _
  · exact ae_of_all _ fun u =>
      (((F.continuous.comp timeSpin_continuous).tendsto _).comp (roundTime_tendsto q hq u))

end SphericalPerceptronFreeEnergy
end

end OAI
