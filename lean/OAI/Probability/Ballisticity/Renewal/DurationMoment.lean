import Mathlib
import OAI.Probability.Ballisticity.Renewal.DurationTail
import OAI.Probability.Ballisticity.Estimates.NaturalTailIntegrable

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma conditioned_wordDuration_integrable {d : ℕ} (hd : 2 ≤ d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    Integrable (fun X => ((firstWord (realPosition (step e)) X).length:ℝ))
      (conditionedLaw ν (realPosition (step e))) := by
  let : IsProbabilityMeasure (conditionedLaw ν (realPosition (step e))) :=
    conditionedLaw_probability ν _ (noDrop_positive_of_directionallyTransient ν _ htrans).ne'
  obtain ⟨A,hA,ht⟩ := duration_polynomial_rapidDecay hd ν hue e htrans
  exact natural_integrable_of_polynomial_rapid_tail _ _
    ((measurable_of_countable List.length).comp (measurable_firstWord _)) A (4*d+2) hA (by omega) ht

lemma conditioned_wordDuration_mean_positive {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (hint : Integrable (fun X => ((firstWord ℓ X).length:ℝ)) (conditionedLaw ν ℓ)) :
    0 < ∫ X, ((firstWord ℓ X).length:ℝ) ∂conditionedLaw ν ℓ := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) :=
    conditionedLaw_probability ν _ (noDrop_positive_of_directionallyTransient ν _ htrans).ne'
  have hge : (1:ℝ) ≤ ∫ X, ((firstWord ℓ X).length:ℝ) ∂conditionedLaw ν ℓ := by
    calc
      (1:ℝ) = ∫ X, (1:ℝ) ∂conditionedLaw ν ℓ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hint (by
        filter_upwards [conditioned_firstWord_exists ν ℓ htrans] with X hX
        have hh := (firstWordEvent_self ℓ X hX).2.2.1
        exact_mod_cast hh)
  linarith

lemma conditioned_word_temporal_strong_law {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (hint : Integrable (fun X => ((firstWord ℓ X).length:ℝ)) (conditionedLaw ν ℓ)) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, Tendsto
      (fun n : ℕ => (regenerationTimes ℓ X n:ℝ)/n) atTop
      (𝓝 (∫ Y, ((firstWord ℓ Y).length:ℝ) ∂conditionedLaw ν ℓ)) := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) :=
    conditionedLaw_probability ν _ (noDrop_positive_of_directionallyTransient ν _ htrans).ne'
  have hm : Measurable (fun w : List (Direction d) => (w.length:ℝ)) := measurable_of_countable _
  have ht := strong_law_ae_real (fun n X => ((regenerationWords ℓ X n).length:ℝ)) hint
    (fun i j hij => ((regenerationWords_independent ν ℓ htrans).indepFun hij).comp hm hm)
    (fun i => (regenerationWords_identDistrib ν ℓ htrans i).comp hm)
  simpa only [regenerationTimes,Nat.cast_sum,regenerationWords,Function.iterate_zero,id_eq] using ht

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma scalar_cut_speed (T : ℕ → ℕ) (hT : StrictMono T) (hT0 : T 0=0)
    (Y R : ℕ → ℝ) (m t : ℝ) (ht : 0 < t)
    (hTime : Tendsto (fun n : ℕ => (T n:ℝ)/n) atTop (𝓝 t))
    (hSpace : Tendsto (fun n : ℕ => Y (T n)/n) atTop (𝓝 m))
    (hR : Tendsto (fun n : ℕ => R n/n) atTop (𝓝 0))
    (herr : ∀ k n, T k ≤ n → n < T (k+1) → |Y n-Y (T k)| ≤ R k) :
    Tendsto (fun n : ℕ => Y n/n) atTop (𝓝 (m/t)) := by
  choose K hK using increasing_cuts_cover T hT hT0
  have hKt := increasing_cuts_index_tendsto T K hT hK
  have hr : Tendsto (fun n : ℕ => ((n:ℝ)+1)/n) atTop (𝓝 1) := by
    have hh := (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1).inv₀ (by norm_num : (1:ℝ) ≠ 0)
    simpa only [inv_one,inv_div] using hh
  have hsucc : Tendsto (fun n : ℕ => (T (n+1):ℝ)/n) atTop (𝓝 t) := by
    have hh := (hTime.comp (tendsto_add_atTop_nat 1)).mul hr
    simp only [mul_one] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
    simp only [Function.comp_def,Nat.cast_add,Nat.cast_one]
    field_simp
  have hden : Tendsto (fun n : ℕ => (n:ℝ)/K n) atTop (𝓝 t) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (hTime.comp hKt) (hsucc.comp hKt)
    · intro n
      change (T (K n):ℝ)/(K n:ℝ) ≤ (n:ℝ)/(K n:ℝ)
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hK n).1) (Nat.cast_nonneg _)
    · intro n
      change (n:ℝ)/(K n:ℝ) ≤ (T (K n+1):ℝ)/(K n:ℝ)
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hK n).2.le) (Nat.cast_nonneg _)
  have hnum : Tendsto (fun n : ℕ => Y n/K n) atTop (𝓝 m) := by
    have hlo := (hSpace.sub hR).comp hKt
    have hhi := (hSpace.add hR).comp hKt
    simp only [sub_zero,add_zero] at hlo hhi
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    · intro n
      have hh := (abs_le.mp (herr (K n) n (hK n).1 (hK n).2)).1
      have hb : Y (T (K n))-R (K n) ≤ Y n := by linarith
      simpa only [sub_div,Function.comp_def] using div_le_div_of_nonneg_right hb (Nat.cast_nonneg (K n))
    · intro n
      have hh := (abs_le.mp (herr (K n) n (hK n).1 (hK n).2)).2
      have hb : Y n ≤ Y (T (K n))+R (K n) := by linarith
      simpa only [add_div,Function.comp_def] using div_le_div_of_nonneg_right hb (Nat.cast_nonneg (K n))
  apply (hnum.div hden ht.ne').congr'
  filter_upwards [hKt.eventually (eventually_gt_atTop (0:ℕ)),eventually_gt_atTop (0:ℕ)] with n hn hn'
  have hk : (K n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn'.ne'
  change (Y n/(K n:ℝ))/((n:ℝ)/(K n:ℝ)) = Y n/(n:ℝ)
  field_simp

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def VelocityPaths {d : ℕ} (v : Vector d) : Set (Path d) :=
  {X | Tendsto (fun n : ℕ => fun i => (X n i:ℝ)/(n:ℝ)) atTop (𝓝 v)}

lemma measurableSet_velocityPaths {d : ℕ} (v : Vector d) : MeasurableSet (VelocityPaths v) := by
  apply measurableSet_tendsto
  intro n
  exact (measurable_of_countable (fun y : Lattice d => fun i => (y i:ℝ)/(n:ℝ))).comp
    (measurable_pi_apply n)

lemma velocityPaths_of_suffix {d : ℕ} (v : Vector d) (X : Path d) (n : ℕ)
    (ht : (fun j => X (n+j)-X n) ∈ VelocityPaths v) : X ∈ VelocityPaths v := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hh := tendsto_pi_nhds.mp ht i
  have hz : Tendsto (fun j : ℕ => (X n i:ℝ)/j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)) :
        Tendsto (fun j : ℕ => (X n i:ℝ)*(j:ℝ)⁻¹) atTop (𝓝 ((X n i:ℝ)*0)))
  have hs : Tendsto (fun j : ℕ => (X (n+j) i:ℝ)/j) atTop (𝓝 (v i)) := by
    convert hh.add hz using 1 <;> simp [Pi.sub_apply,Int.cast_sub,sub_div]
  have hp := hs.mul (tendsto_natCast_div_add_atTop (𝕜 := ℝ) (n:ℝ))
  simp only [mul_one] at hp
  apply (tendsto_add_atTop_iff_nat n).mp
  apply hp.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with j hj
  have hj' : (j:ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  change (X (n+j) i:ℝ)/(j:ℝ) * ((j:ℝ)/((j:ℝ)+(n:ℝ))) =
    (X (j+n) i:ℝ)/(j+n:ℕ)
  rw [Nat.add_comm j n]
  simp only [Nat.cast_add]
  field_simp
  ring

lemma conditioned_to_annealed_velocity {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (v : Vector d)
    (hv : ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ VelocityPaths v) : HasVelocity ν v := by
  let B := NoDrop ℓ 0 ∩ (VelocityPaths v)ᶜ
  have hB : MeasurableSet B := (measurableSet_noDrop ℓ 0).inter (measurableSet_velocityPaths v).compl
  have hBD : B ⊆ NoDrop ℓ 0 := Set.inter_subset_left
  have hcB : conditionedLaw ν ℓ B=0 := measure_mono_null Set.inter_subset_right (ae_iff.mp hv)
  have haB : annealedLaw ν B=0 := by
    rw [conditionedLaw_apply_of_subset ν ℓ B hB hBD] at hcB
    exact (mul_eq_zero.mp hcB).resolve_left (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
  have hwords : ∀ᵐ X ∂annealedLaw ν, ∀ w : List (Direction d),
      (∀ y ∈ wordDepartures 0 w, dot (realPosition y) ℓ <
        dot (realPosition (wordPath 0 w w.length)) ℓ) →
      X ∈ wordCylinder 0 w →
      (fun j => X (w.length+j)-wordPath 0 w w.length) ∉ B := by
    apply ae_all_iff.mpr
    intro w
    by_cases hw : ∀ y ∈ wordDepartures 0 w, dot (realPosition y) ℓ <
      dot (realPosition (wordPath 0 w w.length)) ℓ
    · have hz := annealed_record_suffix ν ℓ w hw B hB hBD
      rw [haB,mul_zero] at hz
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with X hX _ hcy
      exact fun hh => hX ⟨hh,hcy⟩
    · exact Eventually.of_forall fun _ h _ => (hw h).elim
  filter_upwards [annealed_initial ν,annealed_nearest_neighbor ν,
    annealed_trueRecords_unbounded ν ℓ htrans,hwords] with X h0 hNN hrec hwords
  obtain ⟨n,_,hn⟩ := hrec 0
  obtain ⟨w,hw,hcy⟩ := exists_word_prefix X hNN n
  rw [h0] at hcy
  have hwend : wordPath 0 w w.length=X n := by rw [← hw]; exact (hcy _ le_rfl).symm
  have hwrec : ∀ y ∈ wordDepartures 0 w, dot (realPosition y) ℓ <
      dot (realPosition (wordPath 0 w w.length)) ℓ := by
    intro y hy
    obtain ⟨j,hj,rfl⟩ := (wordDepartures_mem_iff 0 y w).mp hy
    rw [← hcy j hj.le,hwend]
    exact hn.1 j (by omega)
  have hnot := hwords w hwrec hcy
  have hD : (fun j => X (w.length+j)-wordPath 0 w w.length) ∈ NoDrop ℓ 0 := by
    intro j
    rw [hwend,hw,dot_realPosition_sub]
    have hh := hn.2 j
    simpa only [dot,realPosition,Pi.zero_apply,Int.cast_zero,zero_mul,Finset.sum_const_zero,
      sub_nonneg] using hh
  apply velocityPaths_of_suffix v X n
  by_contra hh
  apply hnot
  refine ⟨hD,?_⟩
  change (fun j => X (w.length+j)-wordPath 0 w w.length) ∉ VelocityPaths v
  rw [hwend,hw]
  exact hh

end DirectionalTransience

end

end OAI
