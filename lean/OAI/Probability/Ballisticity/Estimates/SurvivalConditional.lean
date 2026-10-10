import Mathlib
import OAI.Probability.Ballisticity.Stationary.EpisodeGlobalRetention
import OAI.Probability.Ballisticity.Stationary.EpisodeNumber
import OAI.Probability.Ballisticity.Stationary.StationaryWindowEntropy
import OAI.Probability.Ballisticity.Stationary.ArraySurvival

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma conditional_survivalViolation_bound {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (ω : Environment d) (hmono : Monotone (t ω))
    (hpos : ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k ω≠0)
    (A : EpisodeAuxiliary e) (i : ℤ) (m n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    globalEpisodeAnchors e t ht ω {E | actualArrayMap e t J ((ω,E),A)∈survivalViolation e i m n ε}
      ≤ ENNReal.ofReal ((n:ℝ)⁻¹/ε^2) := by
  let v : HorizontalSpace e → ℝ := fun z => (localSurvival e ω (t ω i) (t ω (i+m)-t ω i) z).toReal
  let μ := globalEpisodeAnchors e t ht ω
  have hm : Measurable v := measurable_of_countable _
  have hle (z : HorizontalSpace e) : |v z|≤1 := by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.one_ne_top (localSurvival_le_one _ _ _ _ _)).trans_eq ENNReal.toReal_one
  have hi : iIndepFun (fun a (E : EpisodeAnchors e) => v (E (i,a))) μ := by
    have h := iIndepFun_infinitePi (P:=fun p : ℤ×ℕ => episodeProfile e t ω p.1)
      (X:=fun (_p : ℤ×ℕ) z => v z) (fun _ => hm)
    exact h.precomp (fun a b hab => Prod.mk.inj hab |>.2)
  have hmean (a : ℕ) : (∫ E, v (E (i,a)) ∂μ) ≤
      (crossingQuenched (realPosition (step e)) 0 (t ω (i+m)) ω /
        crossingQuenched (realPosition (step e)) 0 (t ω i) ω).toReal := by
    have hmp := measurePreserving_eval_infinitePi (fun p : ℤ×ℕ => episodeProfile e t ω p.1) (i,a)
    have he : (∫ E, v (E (i,a)) ∂μ)=∫ z, v z ∂episodeProfile e t ω i := by
      rw [←hmp.map_eq,integral_map hmp.measurable.aemeasurable hm.aestronglyMeasurable]
      rfl
    rw [he]
    have hh := localSurvival_mean e ω (t ω i) (t ω (i+m)-t ω i) (hpos _)
    have hadd : t ω i+(t ω (i+m)-t ω i)=t ω (i+m) :=
      Nat.add_sub_of_le (hmono (by omega))
    simpa only [hadd,episodeProfile,v] using hh
  have he : {E : EpisodeAnchors e | actualArrayMap e t J ((ω,E),A)∈survivalViolation e i m n ε}=
      {E | (crossingQuenched (realPosition (step e)) 0 (t ω (i+m)) ω /
        crossingQuenched (realPosition (step e)) 0 (t ω i) ω).toReal+ε <
        sampleAverage (fun a E => v (E (i,a))) n E} := by
    ext E
    exact actual_survivalViolation_iff e t J ((ω,E),A) hmono hpos i m n hn ε hε
  rw [he]
  exact sampleAverage_upper_tail μ _ (fun a => hm.comp (measurable_pi_apply _))
    (fun a E => hle (E (i,a))) hi n hn _ ε hmean hε

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma arrayContinuation_shift {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayContinuation e Y) : ArrayContinuation e (StationaryCompact.shift Y) := by
  intro i m a H z hH
  have he : arrayWindowHeight e i m (StationaryCompact.shift Y)=arrayWindowHeight e (i+1) m Y := by
    simp only [arrayWindowHeight,StationaryCompact.shift,add_right_comm i _ 1]
  rw [he] at hH
  have hh := h (i+1) m a H z hH
  convert hh using 1
  · rfl
  · simp only [arrayDiscountedProfile,arrayWindowCost,arrayProfileMass,StationaryCompact.shift,
      add_right_comm i _ 1]

lemma actualArrayMap_continuation_ae {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hmono : ∀ ω, Monotone (t ω)) (κ : ℝ≥0) (hκ : 0<κ)
    (hQ : ∀ᵐ ω ∂Q, ∀ y u, κ ≤ (ω y).1 u) :
    ∀ᵐ X ∂episodeInputLaw e ν Q t ht, ArrayContinuation e (actualArrayMap e t J X) := by
  have hm : MeasurableSet {ω : Environment d | ∀ y u, κ ≤ (ω y).1 u} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun y => MeasurableSet.iInter fun u =>
      measurableSet_le measurable_const ((measurable_pi_apply u).comp
        (measurable_subtype_coe.comp (measurable_pi_apply y)))
  have hb := Measure.ae_compProd_of_ae_fst (globalEpisodeAnchors e t ht) hm hQ
  have ha := (Measure.quasiMeasurePreserving_fst
    (μ:=Q.compProd (globalEpisodeAnchors e t ht)) (ν:=episodeAuxiliaryLaw e ν)).ae hb
  filter_upwards [ha] with X hX
  apply actual_arrayContinuation e t J X (hmono _)
  intro k
  exact ne_of_gt ((pos_iff_ne_zero.mpr (pow_ne_zero k (show (κ:ℝ≥0∞)≠0 by exact_mod_cast hκ.ne'))).trans_le
    (coordinate_survival_lower e X.1.1 κ (fun y => hX y e) k))

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)}
  {e f : Direction d} {D : ℝ}

lemma paddedTimes_int_mono [IsProbabilityMeasure ν]
    (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (ω : Environment d) : Monotone (C.paddedTimes hef N ω) := by
  intro i j hij
  exact episodeBoundary_mono (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω (Int.toNat_le_toNat hij)

variable [IsProbabilityMeasure ν]

lemma bad_limit_continuation (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (Ns : ℕ → ℕ) (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ArrayContinuation e Y := by
  apply closed_support_weak_limit _ ρ hlim _ (arrayContinuation_closed e)
  intro n
  apply actualOccupation_ae_of_ae_invariant e ν _
    (C.paddedTimes hef (Ns n)) (C.paddedStages hef (Ns n))
    (C.paddedTimes_measurable hef (Ns n)) (C.paddedStages_measurable hef (Ns n)) (Ns n)
    (C.activeCount hef (Ns n)) (C.bad_raw_mass_pos hef (Ns n) (hN n) (hmass n)) _
    (arrayContinuation_closed e).measurableSet
  · exact actualArrayMap_continuation_ae e ν _ _ _ (C.paddedTimes_measurable hef (Ns n))
      (C.paddedTimes_int_mono hef (Ns n)) C.κ C.hκ0
      ((cond_absolutelyContinuous (μ:=environmentLaw ν)
        (s:=badCrossingEvent e (Ns n) (1/2))).ae_le C.rows)
  · exact arrayContinuation_shift e

end OperationalConstants
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma survivalViolation_shift {d : ℕ} (e : Direction d) (i : ℤ) (m n : ℕ) (ε : ℝ)
    (Y : ActualEpisodeArray e) :
    StationaryCompact.shift Y∈survivalViolation e i m n ε ↔ Y∈survivalViolation e (i+1) m n ε := by
  simp only [survivalViolation,Set.mem_ofPred_eq,arrayWindowHeight,arraySurvivalThreshold,
    arrayWindowCost,arraySurvivalSum,StationaryCompact.shift,add_right_comm i _ 1]
  rfl

lemma survivalViolation_iterate {d : ℕ} (e : Direction d) (i : ℤ) (m n : ℕ) (ε : ℝ)
    (Y : ActualEpisodeArray e) (j : ℕ) :
    StationaryCompact.shift^[j] Y∈survivalViolation e i m n ε ↔ Y∈survivalViolation e (i+j) m n ε := by
  induction j generalizing i with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',survivalViolation_shift,ih]
    rw [show i+1+(j:ℤ)=i+(j+1:ℕ) by omega]

lemma input_survivalViolation_bound {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i)
    (hgood : ∀ᵐ ω ∂Q, Monotone (t ω) ∧ ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k ω≠0)
    (i : ℤ) (m n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    episodeInputLaw e ν Q t ht {X | actualArrayMap e t J X∈survivalViolation e i m n ε} ≤
      ENNReal.ofReal ((n:ℝ)⁻¹/ε^2)*Q Set.univ := by
  have hs : MeasurableSet {X : EpisodeInput e | actualArrayMap e t J X∈survivalViolation e i m n ε} :=
    (survivalViolation_open e i m n ε).measurableSet.preimage (actualArrayMap_measurable e t J ht hJ)
  rw [episodeInputLaw,Measure.prod_apply_symm hs]
  calc
    _ ≤ ∫⁻ _A, ENNReal.ofReal ((n:ℝ)⁻¹/ε^2)*Q Set.univ ∂episodeAuxiliaryLaw e ν := by
      apply lintegral_mono
      intro A
      dsimp only
      have hsa : MeasurableSet {x : Environment d × EpisodeAnchors e |
          actualArrayMap e t J (x,A) ∈ survivalViolation e i m n ε} :=
        hs.preimage (measurable_id.prodMk measurable_const)
      change (Q ⊗ₘ globalEpisodeAnchors e t ht) {x | actualArrayMap e t J (x,A) ∈ survivalViolation e i m n ε} ≤ _
      rw [Measure.compProd_apply hsa]
      calc
        _ ≤ ∫⁻ _ω, ENNReal.ofReal ((n:ℝ)⁻¹/ε^2) ∂Q := by
          apply lintegral_mono_ae
          filter_upwards [hgood] with ω hω
          exact conditional_survivalViolation_bound e t J ht ω hω.1 hω.2 A i m n hn ε hε
        _ = _ := by simp
    _ = _ := by simp

lemma input_env_mass {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    episodeInputLaw e ν Q t ht Set.univ=Q Set.univ := by
  rw [episodeInputLaw,←Set.univ_prod_univ,Measure.prod_prod]
  simp only [measure_univ,mul_one,Measure.compProd_apply_univ]

lemma actualOccupation_survivalViolation_bound {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (hgood : ∀ᵐ ω ∂Q, Monotone (t ω) ∧ ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k ω≠0)
    (i : ℤ) (m n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    (actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)) (survivalViolation e i m n ε) ≤
      ENNReal.ofReal ((n:ℝ)⁻¹/ε^2) := by
  let s := survivalViolation e i m n ε
  let c := ENNReal.ofReal ((n:ℝ)⁻¹/ε^2)
  have hs : MeasurableSet s := (survivalViolation_open e i m n ε).measurableSet
  have hraw : actualOccupationRaw e ν Q t J ht N M s ≤ c*actualOccupationRaw e ν Q t J ht N M Set.univ := by
    unfold actualOccupationRaw StationaryCompact.episodeOccupationRaw
    rw [Measure.finsetSum_apply _ _ _,Measure.finsetSum_apply _ _ _,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hmap := (StationaryCompact.shift_continuous.measurable.iterate j).comp
      (actualArrayMap_measurable e t J ht hJ)
    change Measurable (fun x => StationaryCompact.shift^[j] (actualArrayMap e t J x)) at hmap
    rw [Measure.map_apply hmap hs,Measure.map_apply hmap MeasurableSet.univ,Set.preimage_univ]
    have hr := episodeInputLaw_restrict e ν Q t ht {ω | j<M ω} (measurableSet_lt measurable_const hM)
    change (episodeInputLaw e ν Q t ht).restrict {x | j < (fun X => M X.1.1) x} = _ at hr
    rw [hr,input_env_mass]
    have he : (fun X : EpisodeInput e => StationaryCompact.shift^[j] (actualArrayMap e t J X)) ⁻¹' s=
        {X | actualArrayMap e t J X∈survivalViolation e (i+j) m n ε} := by
      ext X
      exact survivalViolation_iterate e i m n ε (actualArrayMap e t J X) j
    rw [he]
    exact input_survivalViolation_bound e ν (Q.restrict {ω | j<M ω}) t J ht hJ
      (ae_restrict_of_ae hgood) (i+j) m n hn ε hε
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let ρ : FiniteMeasure (ActualEpisodeArray e) := ⟨actualOccupationRaw e ν Q t J ht N M,inferInstance⟩
  have hmass : (ρ : Measure (ActualEpisodeArray e)) Set.univ≠0 := by
    exact ENNReal.toReal_ne_zero.mp hpos.ne' |>.1
  have hρ : ρ≠0 := by
    intro hz
    exact hmass (by rw [hz]; rfl)
  change (ρ.normalize : Measure (ActualEpisodeArray e)) s ≤ c
  rw [ρ.toMeasure_normalize_eq_of_nonzero hρ,Measure.smul_apply]
  rw [ENNReal.smul_def,ENNReal.coe_inv (ρ.mass_nonzero_iff.mpr hρ)]
  have he : (ρ.mass : ℝ≥0∞)=(ρ : Measure (ActualEpisodeArray e)) Set.univ := by simp
  rw [he,smul_eq_mul]
  calc
    _ ≤ ((ρ : Measure (ActualEpisodeArray e)) Set.univ)⁻¹ *
        (c * (ρ : Measure (ActualEpisodeArray e)) Set.univ) := mul_le_mul
          le_rfl hraw (by positivity) (by positivity)
    _ = c := by rw [mul_left_comm,ENNReal.inv_mul_cancel hmass (measure_ne_top _ _),mul_one]

end DirectionalTransience

end

end OAI
