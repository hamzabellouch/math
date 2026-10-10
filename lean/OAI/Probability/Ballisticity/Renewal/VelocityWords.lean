import Mathlib
import OAI.Probability.Ballisticity.Renewal.DurationMoment

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def renewalVelocity {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) : Vector d :=
  fun i => (∫ X, wordCoordinate (i,true) (firstWord ℓ X) ∂conditionedLaw ν ℓ) /
    (∫ X, ((firstWord ℓ X).length:ℝ) ∂conditionedLaw ν ℓ)

lemma conditioned_velocity_from_duration {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ=1)
    (htrans : DirectionallyTransient ν ℓ)
    (hint : Integrable (fun X => ((firstWord ℓ X).length:ℝ)) (conditionedLaw ν ℓ)) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ VelocityPaths (renewalVelocity ν ℓ) := by
  have ht := conditioned_wordDuration_mean_positive ν ℓ htrans hint
  filter_upwards [conditioned_regenerationSupport ν ℓ htrans,
    conditioned_word_temporal_strong_law ν ℓ htrans hint,
    ae_all_iff.mpr (fun i : Fin d => conditioned_word_spatial_strong_laws ν hue ℓ hℓ htrans (i,true))]
      with X hX hTime hSpace
  apply tendsto_pi_nhds.mpr
  intro i
  change Tendsto (fun n : ℕ => signedCoordinate (i,true) (X n)/n) atTop (𝓝 _)
  apply scalar_cut_speed (regenerationTimes ℓ X) (regenerationTimes_strictMono ℓ X hX.2)
    (regenerationTimes_zero ℓ X) (fun n => signedCoordinate (i,true) (X n))
    (fun n => wordRadius (regenerationWords ℓ X n)) _ _ ht hTime
  · simpa only [regeneration_coordinate_sum ℓ (i,true) X hX] using (hSpace i).1
  · exact (hSpace i).2
  · intro k n hlo hhi
    have hnk : n=regenerationTimes ℓ X k+(n-regenerationTimes ℓ X k) := by omega
    have hlen : n-regenerationTimes ℓ X k ≤ (regenerationWords ℓ X k).length := by
      rw [regenerationTimes_succ] at hhi
      omega
    have hh := regeneration_span ℓ X hX.1 hX.2 k _ hlen
    rw [← hnk] at hh
    rw [hh,signedCoordinate_add,add_sub_cancel_left]
    exact (signedCoordinate_abs_le_norm _ _).trans (wordRadius_bound _ hlen)

lemma renewalVelocity_projection {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ=1)
    (htrans : DirectionallyTransient ν ℓ) :
    dot (renewalVelocity ν ℓ) ℓ =
      (∫ X, wordHeightGain ℓ (firstWord ℓ X) ∂conditionedLaw ν ℓ) /
        (∫ X, ((firstWord ℓ X).length:ℝ) ∂conditionedLaw ν ℓ) := by
  have hint (i : Fin d) : Integrable (fun X => wordCoordinate (i,true) (firstWord ℓ X)*ℓ i)
      (conditionedLaw ν ℓ) := (conditioned_wordCoordinate_integrable ν hue ℓ hℓ htrans (i,true)).mul_const _
  have hid : (∫ X, wordHeightGain ℓ (firstWord ℓ X) ∂conditionedLaw ν ℓ) =
      ∑ i : Fin d, (∫ X, wordCoordinate (i,true) (firstWord ℓ X) ∂conditionedLaw ν ℓ)*ℓ i := by
    change (∫ X, ∑ i : Fin d, wordCoordinate (i,true) (firstWord ℓ X)*ℓ i ∂conditionedLaw ν ℓ)=_
    rw [integral_finsetSum _ (fun i _ => hint i)]
    exact Finset.sum_congr rfl (fun i _ => integral_mul_const _ _)
  rw [hid,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  change (_ / _)*_=(_*_)/_
  ring

lemma velocity_from_integrable_words {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ=1)
    (htrans : DirectionallyTransient ν ℓ)
    (hint : Integrable (fun X => ((firstWord ℓ X).length:ℝ)) (conditionedLaw ν ℓ)) :
    0 < dot (renewalVelocity ν ℓ) ℓ ∧ HasVelocity ν (renewalVelocity ν ℓ) := by
  constructor
  · rw [renewalVelocity_projection ν hue ℓ hℓ htrans]
    exact div_pos (conditioned_wordHeightGain_moments ν ℓ (unit_direction_coordinate_bound ℓ hℓ) htrans).2.1
      (conditioned_wordDuration_mean_positive ν ℓ htrans hint)
  · exact conditioned_to_annealed_velocity ν ℓ htrans _
      (conditioned_velocity_from_duration ν hue ℓ hℓ htrans hint)

lemma signed_coordinate_ballisticity {d : ℕ} (hd : 2 ≤ d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ v : Vector d, 0 < dot v (realPosition (step e)) ∧ HasVelocity ν v := by
  exact ⟨renewalVelocity ν (realPosition (step e)),velocity_from_integrable_words ν hue _
    (signed_direction_unit e) htrans (conditioned_wordDuration_integrable hd ν hue e htrans)⟩

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma velocityPaths_projection {d : ℕ} (v ℓ : Vector d) (X : Path d)
    (hX : X ∈ VelocityPaths v) :
    Tendsto (fun n : ℕ => dot (realPosition (X n)) ℓ/(n:ℝ)) atTop (𝓝 (dot v ℓ)) := by
  have hh := tendsto_finsetSum Finset.univ (fun i _ =>
    (tendsto_pi_nhds.mp hX i).mul_const (ℓ i))
  simpa only [dot,realPosition,Finset.sum_div,div_mul_eq_mul_div] using hh

lemma conditioned_word_height_strong_law {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hℓ : dot ℓ ℓ=1) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, Tendsto
      (fun n : ℕ => dot (realPosition (X (regenerationTimes ℓ X n))) ℓ/n) atTop
      (𝓝 (∫ Y, wordHeightGain ℓ (firstWord ℓ Y) ∂conditionedLaw ν ℓ)) := by
  have hm : Measurable (wordHeightGain ℓ) := measurable_of_countable _
  have ht := strong_law_ae_real (fun n X => wordHeightGain ℓ (regenerationWords ℓ X n))
    (conditioned_wordHeightGain_moments ν ℓ (unit_direction_coordinate_bound ℓ hℓ) htrans).1
    (fun i j hij => ((regenerationWords_independent ν ℓ htrans).indepFun hij).comp hm hm)
    (fun i => (regenerationWords_identDistrib ν ℓ htrans i).comp hm)
  filter_upwards [conditioned_regenerationSupport ν ℓ htrans,ht] with X hX ht
  simpa only [regeneration_height_sum ℓ X hX.1 hX.2,regenerationWords,Function.iterate_zero,id_eq] using ht

lemma velocity_positive_original_direction {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ=1)
    (htrans : DirectionallyTransient ν ℓ) (e : Direction d)
    (he : 0 < ∫ X, wordCoordinate e (firstWord ℓ X) ∂conditionedLaw ν ℓ)
    (v : Vector d) (hv : HasVelocity ν v) (hve : 0 < dot v (realPosition (step e))) :
    0 < dot v ℓ := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) :=
    conditionedLaw_probability ν _ (noDrop_positive_of_directionallyTransient ν _ htrans).ne'
  have hvc : ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ VelocityPaths v :=
    (conditionedLaw_absolutelyContinuous ν ℓ).ae_le hv
  have hfull := (conditioned_regenerationSupport ν ℓ htrans).and
    ((conditioned_word_height_strong_law ν ℓ hℓ htrans).and
      ((conditioned_word_spatial_strong_laws ν hue ℓ hℓ htrans e).and hvc))
  obtain ⟨X,hX,hH,hC,hvX⟩ := hfull.exists
  have hT := (regenerationTimes_strictMono ℓ X hX.2).tendsto_atTop
  have hvH := (velocityPaths_projection v ℓ X hvX).comp hT
  have hvC := (velocityPaths_projection v (realPosition (step e)) X hvX).comp hT
  simp only [Function.comp_def,dot_signed_direction] at hvC
  have hC' : Tendsto (fun n : ℕ => signedCoordinate e (X (regenerationTimes ℓ X n))/n)
      atTop (𝓝 (∫ Y, wordCoordinate e (firstWord ℓ Y) ∂conditionedLaw ν ℓ)) := by
    simpa only [regeneration_coordinate_sum ℓ e X hX] using hC.1
  have hp := hH.mul hvC
  have hq := hC'.mul hvH
  have hid : (fun n : ℕ =>
      (dot (realPosition (X (regenerationTimes ℓ X n))) ℓ/(n:ℝ)) *
      (signedCoordinate e (X (regenerationTimes ℓ X n))/(regenerationTimes ℓ X n:ℝ))) =
      (fun n : ℕ => (signedCoordinate e (X (regenerationTimes ℓ X n))/(n:ℝ)) *
      (dot (realPosition (X (regenerationTimes ℓ X n))) ℓ/(regenerationTimes ℓ X n:ℝ))) := by
    funext n
    ring
  simp only [Function.comp_def] at hp hq
  rw [hid] at hp
  have hlim := tendsto_nhds_unique hp hq
  have hh := (conditioned_wordHeightGain_moments ν ℓ
    (unit_direction_coordinate_bound ℓ hℓ) htrans).2.1
  have hm : 0 < (∫ X, wordCoordinate e (firstWord ℓ X) ∂conditionedLaw ν ℓ)*dot v ℓ := by
    rw [← hlim]
    exact mul_pos hh hve
  exact (mul_pos_iff.mp hm).resolve_right (fun h => (not_lt_of_ge he.le h.1)) |>.2

theorem directional_transience_implies_ballisticity_unit {d : ℕ} (hd : 2 ≤ d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (ℓ : Vector d) (hℓ : dot ℓ ℓ=1) (htrans : DirectionallyTransient ν ℓ) :
    ∃ v : Vector d, 0 < dot v ℓ ∧ HasVelocity ν v := by
  obtain ⟨e,he⟩ := conditioned_coordinate_positive_mean ν hue ℓ hℓ htrans
  have hte : DirectionallyTransient ν (realPosition (step e)) := by
    apply conditioned_to_annealed_transience ν ℓ _ htrans
    simpa only [TransientPaths,Set.mem_ofPred_eq,dot_signed_direction] using
      conditioned_coordinate_transience ν hue ℓ hℓ htrans e he
  obtain ⟨v,hve,hv⟩ := signed_coordinate_ballisticity hd ν hue e hte
  exact ⟨v,velocity_positive_original_direction ν hue ℓ hℓ htrans e he v hv hve,hv⟩

end DirectionalTransience

end

end OAI
