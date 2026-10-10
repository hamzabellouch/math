import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.OptionalPastPalm
import OAI.Probability.SLEGauge.MomentBatches

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace SLEExactGauge.MomentBatches

lemma sum_repeated_thresholds (l : List ℤ) (N : ℤ → ℕ) (f : ℝ → ℝ) :
    ((l.flatMap (fun k => List.replicate (N k) ((2:ℝ)^k))).map f).sum =
      (l.map (fun k => (N k:ℝ)*f ((2:ℝ)^k))).sum := by
  induction l with
  | nil => simp
  | cons k l ih => simpa [List.sum_replicate,nsmul_eq_mul] using congrArg ((N k:ℝ)*f ((2:ℝ)^k)+·) ih

lemma noncleanup_sum (m : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ) :
    ((noncleanup m n).map f).sum =
      ∑ k∈support m n, (multiplicity m n k:ℝ)*f ((2:ℝ)^k) := by
  rw [noncleanup,sum_repeated_thresholds]
  simpa only [Finset.sort_toFinset] using
    (List.sum_toFinset (fun k => (multiplicity m n k:ℝ)*f ((2:ℝ)^k))
      ((support m n).sort_nodup (· ≤ ·))).symm

lemma batch_sum (m : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ) :
    ((batch m n).map f).sum =
      (∑ k∈support m n, (multiplicity m n k:ℝ)*f ((2:ℝ)^k)) + f n := by
  simp only [batch,List.map_append,List.map_cons,List.map_nil,List.sum_append,
    List.sum_cons,List.sum_nil,add_zero,noncleanup_sum]

lemma fin_sum_batch (m : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ) :
    (∑ i : Fin (batch m n).length, f ((batch m n)[i.1])) =
      ((batch m n).map f).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn (f ∘ (fun i : Fin (batch m n).length => (batch m n)[i.1]))).sum = _
  rw [← List.map_ofFn,List.ofFn_getElem]

 

lemma cleanup_counts_le (S : Finset ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∑ n∈S, if 16*((n:ℝ)+1) ≤ x then (1:ℝ) else 0) ≤ x/16 := by
  classical
  let A : Finset ℕ := S.filter (fun n : ℕ => 16*((n:ℝ)+1) ≤ x)
  have hsub : A ⊆ Finset.range ⌊x/16⌋₊ := by
    intro n hn
    rw [Finset.mem_range]
    have hh := (Finset.mem_filter.mp hn).2
    have hf : n+1 ≤ ⌊x/16⌋₊ := Nat.le_floor (by push_cast; linarith)
    omega
  calc
    (∑ n∈S, if 16*((n:ℝ)+1) ≤ x then (1:ℝ) else 0) = (A.card:ℝ) := by
      rw [← Finset.sum_filter]
      simp [A]
    _ ≤ (⌊x/16⌋₊:ℝ) := by exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
    _ ≤ x/16 := Nat.floor_le (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma cleanup_sum_le (L : Ω → ℝ) (hL : Measurable L) (hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω)
    (hInt : Integrable L P) (S : Finset ℕ) :
    (∑ n∈S, P.real {ω | 16*((n:ℝ)+1) ≤ L ω}) ≤ moment P L 1/16 := by
  let f (n : ℕ) := {ω | 16*((n:ℝ)+1) ≤ L ω}.indicator (fun _ : Ω => (1:ℝ))
  have hint (n : ℕ) : Integrable (f n) P :=
    (integrable_const 1).indicator (measurableSet_le measurable_const hL)
  have he (n : ℕ) : (∫ ω, f n ω ∂P)=P.real {ω | 16*((n:ℝ)+1) ≤ L ω} := by
    rw [integral_indicator_const _ (measurableSet_le measurable_const hL),smul_eq_mul,mul_one]
  have hpoint : (fun ω => ∑ n∈S, f n ω) ≤ᵐ[P] (fun ω => L ω/16) :=
    hL0.mono fun ω hω => cleanup_counts_le S hω
  have hI := integral_mono_ae (integrable_finsetSum _ (fun n hn => hint n)) (hInt.div_const 16) hpoint
  rw [integral_finsetSum _ (fun n hn => hint n),integral_div] at hI
  simpa only [he,moment,pow_one] using hI

 

theorem cleanup_tail (L : Ω → ℝ) (hL : Measurable L) (hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω)
    (hInt : Integrable L P) :
    Summable (fun n : ℕ => P.real {ω | 16*((n:ℝ)+1) ≤ L ω}) ∧
    (∑' n : ℕ, P.real {ω | 16*((n:ℝ)+1) ≤ L ω}) ≤ moment P L 1/16 :=
  ⟨summable_of_sum_le (fun _ => measureReal_nonneg) (cleanup_sum_le P L hL hL0 hInt),
   Real.tsum_le_of_sum_le (fun _ => measureReal_nonneg) (cleanup_sum_le P L hL hL0 hInt)⟩

lemma upper_tail_bound_geometric (n : ℕ) (hn : 0 < n) :
    (4:ℝ)^n/(16:ℝ)^n/(1-(1/2:ℝ)^n) ≤ 2*(1/4:ℝ)^n := by
  have hq : (1/2:ℝ)^n ≤ 1/2 := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
      (show 1 ≤ n from hn)
  have hden : (1/2:ℝ) ≤ 1-(1/2:ℝ)^n := by linarith
  rw [← div_pow]
  norm_num only [show (4:ℝ)/16=1/4 by norm_num]
  calc
    (1/4:ℝ)^n/(1-(1/2:ℝ)^n) ≤ (1/4:ℝ)^n/(1/2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = 2*(1/4:ℝ)^n := by ring

lemma summable_noncleanup_tails (L : Ω → ℝ) (hL : Measurable L) (hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω)
    (hint : ∀ n, Integrable (fun ω => (L ω)^n) P) (hmean : 0 < moment P L 1) :
    Summable (fun n : ℕ =>
      (((noncleanup (moment P L) (n+1)).map (fun b => P.real {ω | 16*b ≤ L ω})).sum)) := by
  have hgeom := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4)
    (by norm_num : (1/4:ℝ)<1)).mul_left 2
  have hgeom' : Summable (fun n : ℕ => 2*(1/4:ℝ)^(n+1)) :=
    hgeom.comp_injective Nat.succ_injective
  apply Summable.of_nonneg_of_le _ _ hgeom'
  · intro n
    exact List.sum_nonneg (by intro x hx; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; exact measureReal_nonneg)
  · intro n
    rw [noncleanup_sum]
    obtain ⟨hm,hJ⟩ := moment_sequence_properties P L hL0 hint hmean
    exact (upper_tail_finite P L hL hL0 (n+1) (by omega) (hint (n+1)) (hm (n+1) (by omega))).trans
      (upper_tail_bound_geometric (n+1) (by omega))

 

theorem summable_batch_tails (L : Ω → ℝ) (hL : Measurable L) (hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω)
    (hint : ∀ n, Integrable (fun ω => (L ω)^n) P) (hmean : 0 < moment P L 1) :
    Summable (fun n : ℕ =>
      (((batch (moment P L) (n+1)).map (fun b => P.real {ω | 16*b ≤ L ω})).sum)) := by
  have hInt : Integrable L P := by simpa only [pow_one] using hint 1
  have hs := (summable_noncleanup_tails P L hL hL0 hint hmean).add
    (cleanup_tail P L hL hL0 hInt).1
  simpa only [batch,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,Nat.cast_add,Nat.cast_one] using hs

 
theorem summable_entry_tails (L : Ω → ℝ) (hL : Measurable L) (hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω)
    (hint : ∀ n, Integrable (fun ω => (L ω)^n) P) (hmean : 0 < moment P L 1) :
    Summable (fun i : EntryIndex (moment P L) => P.real {ω | 16*threshold (moment P L) i ≤ L ω}) := by
  have hs := summable_batch_tails P L hL hL0 hint hmean
  have hinj : Function.Injective (fun n : {n : ℕ // 0 < n} => n.val-1) := by
    intro n j h
    have hn := n.property
    have hj := j.property
    change n.val-1=j.val-1 at h
    apply Subtype.ext
    omega
  have hs' := hs.comp_injective hinj
  have hseq : Summable (fun n : {n : ℕ // 0 < n} =>
      (((batch (moment P L) n.val).map (fun b => P.real {ω | 16*b ≤ L ω})).sum)) := by
    apply hs'.congr
    intro n
    dsimp only [Function.comp_apply]
    rw [Nat.sub_add_cancel n.property]
  apply (summable_sigma_of_nonneg (fun i => measureReal_nonneg)).mpr
  refine ⟨fun n => (hasSum_fintype _).summable,?_⟩
  apply hseq.congr
  intro n
  rw [tsum_fintype]
  exact (fin_sum_batch (moment P L) n.val (fun b => P.real {ω | 16*b ≤ L ω})).symm

 

theorem tail_summability (L : Ω → ℝ) (hL : Measurable L) (hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω)
    (hint : ∀ n, Integrable (fun ω => (L ω)^n) P) (hmean : 0 < moment P L 1) :
    (∑' i : EntryIndex (moment P L), P {ω | 16*threshold (moment P L) i ≤ L ω}) < ∞ := by
  have h := (summable_entry_tails P L hL hL0 hint hmean).tsum_ofReal_lt_top
  simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top P _)] using h

end SLEExactGauge.MomentBatches
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace SLEExactGauge.MomentBatches

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

lemma increasing_level_bounds (L : Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (hY0 : ∀ᵐ ω ∂P, ∀ j, 0 ≤ Y j ω)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun j => Y j ω))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun j => Y j ω) atTop (𝓝 (L ω))) :
    ∀ᵐ ω ∂P, ∀ j, 0 ≤ Y j ω ∧ Y j ω ≤ L ω := by
  filter_upwards [hY0,hmono,hlim] with ω h0 hm hl
  exact fun j => ⟨h0 j,hm.ge_of_tendsto hl j⟩

lemma integrable_level_pow (L Y : Ω → ℝ) (hY : Measurable Y)
    (hYL : ∀ᵐ ω ∂P, 0 ≤ Y ω ∧ Y ω ≤ L ω) (n : ℕ)
    (hint : Integrable (fun ω => (L ω)^n) P) :
    Integrable (fun ω => (Y ω)^n) P := by
  refine hint.mono_nonneg (hY.pow_const n).aestronglyMeasurable ?_ ?_
  · exact hYL.mono fun ω hω => pow_nonneg hω.1 n
  · exact hYL.mono fun ω hω => pow_le_pow_left₀ hω.1 hω.2 n

 

theorem increasing_moments (L : Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j))
    (hY0 : ∀ᵐ ω ∂P, ∀ j, 0 ≤ Y j ω)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun j => Y j ω))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun j => Y j ω) atTop (𝓝 (L ω)))
    (n : ℕ) (hint : Integrable (fun ω => (L ω)^n) P) :
    (∀ j, Integrable (fun ω => (Y j ω)^n) P) ∧
    Monotone (fun j => moment P (Y j) n) ∧
    Tendsto (fun j => moment P (Y j) n) atTop (𝓝 (moment P L n)) := by
  have hb := increasing_level_bounds P L Y hY0 hmono hlim
  have hI (j : ℕ) : Integrable (fun ω => (Y j ω)^n) P :=
    integrable_level_pow P L (Y j) (hY j) (hb.mono fun ω hω => hω j) n hint
  refine ⟨hI,?_,?_⟩
  · intro j k hjk
    apply integral_mono_ae (hI j) (hI k)
    filter_upwards [hY0,hmono] with ω h0 hm
    exact pow_le_pow_left₀ (h0 j) (hm hjk) n
  · apply tendsto_integral_of_dominated_convergence (fun ω => (L ω)^n)
      (fun j => (hY j |>.pow_const n).aestronglyMeasurable) hint
    · intro j
      filter_upwards [hb] with ω hω
      rw [Real.norm_of_nonneg (pow_nonneg (hω j).1 n)]
      exact pow_le_pow_left₀ (hω j).1 (hω j).2 n
    · exact hlim.mono fun ω hω => hω.pow n

 

lemma level_eq_tsum_indicators {v : ℕ → ℝ} {M : ℝ} (hM : 0 < M)
    (hlim : Tendsto v atTop (𝓝 M)) :
    level v M = 1 + ∑' j : ℕ, if 1 ≤ j ∧ v j ≤ 3*M/4 then 1 else 0 := by
  classical
  have hfin := finite_badLevels hM hlim
  rw [tsum_eq_sum (s := hfin.toFinset) (fun j hj => ?_)]
  · simp only [level,dite_eq_left hfin]
    congr 1
    calc
      hfin.toFinset.card = ∑ _ ∈ hfin.toFinset, (1:ℕ) := by simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : 1 ≤ j ∧ v j ≤ 3*M/4 := by
          simpa only [Finite.mem_toFinset,badLevels,mem_ofPred_eq] using hj
        simp only [ite_eq_left hj']
  · have hnj : ¬ (1 ≤ j ∧ v j ≤ 3*M/4) := by
      simpa only [Finite.mem_toFinset,badLevels,mem_ofPred_eq] using hj
    exact ite_eq_right hnj

 

def momentLevel (L : Ω → ℝ) (Y : ℕ → Ω → ℝ) (n : ℕ) : ℕ :=
  level (fun j => moment P (Y j) n) (moment P L n)

def fullMomentGauge (L : Ω → ℝ) (Y : ℕ → Ω → ℝ) (a d : ℝ) : ℝ → ℝ :=
  momentGauge (moment P L) a d (momentLevel P L Y)

variable [IsProbabilityMeasure P]

 

theorem selected_level_moment (L : Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j))
    (hY0 : ∀ᵐ ω ∂P, ∀ j, 0 ≤ Y j ω)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun j => Y j ω))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun j => Y j ω) atTop (𝓝 (L ω)))
    (hint : ∀ n, Integrable (fun ω => (L ω)^n) P)
    (hmean : 0 < moment P L 1) (n : ℕ) (hn : 0 < n) :
    0 < momentLevel P L Y n ∧
    (badLevels (fun j => moment P (Y j) n) (moment P L n)).Finite ∧
    3*moment P L n/4 < moment P (Y (momentLevel P L Y n)) n := by
  have hb := increasing_level_bounds P L Y hY0 hmono hlim
  have hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω := hb.mono fun ω hω => (hω 0).1.trans (hω 0).2
  have hm := (moment_sequence_properties P L hL0 hint hmean).1 n hn
  obtain ⟨hI,hmn,hlimn⟩ := increasing_moments P L Y hY hY0 hmono hlim n (hint n)
  exact ⟨level_pos _ _,finite_badLevels hm hlimn,level_moment_gt hm hmn hlimn⟩

 

theorem success_selected_level (L : Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ j, Measurable (Y j))
    (hY0 : ∀ᵐ ω ∂P, ∀ j, 0 ≤ Y j ω)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun j => Y j ω))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun j => Y j ω) atTop (𝓝 (L ω)))
    (hint : ∀ n, Integrable (fun ω => (L ω)^n) P)
    (hmean : 0 < moment P L 1) (n : ℕ) (hn : 3 ≤ n) :
    (2:ℝ)^(n-2)-1/(2*(1-(1/2:ℝ)^n)) ≤
      (∑' k : ℤ, (multiplicity (moment P L) n k:ℝ)*
        P.real {ω | (2:ℝ)^k ≤ Y (momentLevel P L Y n) ω}) ∧
    (2:ℝ)^n/8 ≤ (2:ℝ)^(n-2)-1/(2*(1-(1/2:ℝ)^n)) := by
  have hb := (increasing_level_bounds P L Y hY0 hmono hlim).mono
    (fun ω hω => hω (momentLevel P L Y n))
  exact success P L (Y (momentLevel P L Y n)) (hY _) hb hint hmean n hn
    (integrable_level_pow P L _ (hY _) hb n (hint n))
    (selected_level_moment P L Y hY hY0 hmono hlim hint hmean n (by omega)).2.2.le

 

theorem fullMomentGauge_properties (L : Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (hL0 : ∀ᵐ ω ∂P, 0 ≤ L ω)
    (hint : ∀ n, Integrable (fun ω => (L ω)^n) P)
    (hmean : 0 < moment P L 1) {a d : ℝ}
    (ha : 0 ≤ a) (hd : 0 < d) (hd2 : d ≤ 2) :
    Target.IsHausdorffGauge (fullMomentGauge P L Y a d) ∧
    ∀ C r : ℝ, 1 ≤ C → 0 ≤ r →
      fullMomentGauge P L Y a d (C*r) ≤ C^2*fullMomentGauge P L Y a d r := by
  obtain ⟨hm,hJ⟩ := moment_sequence_properties P L hL0 hint hmean
  exact ⟨momentGauge_admissible _ hm hJ ha hd hd2 _,
    fun C r hC _ => momentGauge_doubling _ hm hJ a d _ hC⟩

end SLEExactGauge.MomentBatches
end
end
 

 
section
 

noncomputable section
open MeasureTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions CompactSequence
open MomentBatches

def sequenceMassReal (x : ℕ→ℝ≥0∞) : ℝ := (diskSequenceMass x).toReal
def sequenceLevelReal (l : ℕ) (x : ℕ→ℝ≥0∞) : ℝ := (x l).toReal

lemma sequenceMassReal_measurable : Measurable sequenceMassReal :=
  diskSequenceMass_measurable.ennreal_toReal

lemma sequenceLevelReal_measurable (l : ℕ) : Measurable (sequenceLevelReal l) :=
  (measurable_pi_apply l).ennreal_toReal

lemma sequenceMassReal_nonneg (x : ℕ→ℝ≥0∞) : 0 ≤ sequenceMassReal x := ENNReal.toReal_nonneg
lemma sequenceLevelReal_nonneg (l : ℕ) (x : ℕ→ℝ≥0∞) : 0 ≤ sequenceLevelReal l x :=
  ENNReal.toReal_nonneg

lemma sequenceReal_monotone {x : ℕ→ℝ≥0∞} (hmono : Monotone x)
    (hfin : diskSequenceMass x<∞) : Monotone (fun l=>sequenceLevelReal l x) := by
  intro l k hlk
  exact ENNReal.toReal_mono ((le_iSup x k).trans_lt hfin).ne (hmono hlk)

lemma sequenceReal_tendsto {x : ℕ→ℝ≥0∞} (hmono : Monotone x)
    (hfin : diskSequenceMass x<∞) :
    Tendsto (fun l=>sequenceLevelReal l x) atTop (𝓝 (sequenceMassReal x)) :=
  (ENNReal.tendsto_toReal hfin.ne).comp (diskSequenceMass_tendsto hmono)

lemma sequenceMassReal_integrable_pow (Q : Measure (ℕ→ℝ≥0∞))
    (m : ℕ) (hf : (∫⁻x,diskSequenceMass x^m∂Q)<∞) :
    Integrable (fun x=>sequenceMassReal x^m) Q := by
  simpa only [ENNReal.toReal_pow, sequenceMassReal] using
    integrable_toReal_of_lintegral_ne_top
      (diskSequenceMass_measurable.pow_const m).aemeasurable hf.ne

lemma sequenceMassReal_moment (Q : Measure (ℕ→ℝ≥0∞))
    (hfin : ∀ᵐ x∂Q,diskSequenceMass x<∞) (m : ℕ) :
    moment Q sequenceMassReal m=(∫⁻x,diskSequenceMass x^m∂Q).toReal := by
  unfold moment sequenceMassReal
  simp only [←ENNReal.toReal_pow]
  exact integral_toReal (diskSequenceMass_measurable.pow_const m).aemeasurable
    (hfin.mono (fun _ hx=>ENNReal.pow_lt_top hx))

lemma sequenceLevelReal_moment (W : Measure GDriver) (a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→GDriver→Measure UpperPlane)
    (hμ : Measurable (fun p : ℝ≥0∞×GDriver=>μ p.1 p.2))
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)]
    (r : ℝ) (Q : Measure (ℕ→ℝ≥0∞))
    (hQlaw : ∀n,Q.map (initialVector n)=(finiteAngleLaw W a n).map
      (fun p=>fun i : Fin (n+1)=>subdiskMass a μ r i p))
    (hfin : ∀ᵐ x∂Q,diskSequenceMass x<∞) (m l : ℕ) :
    moment Q (sequenceLevelReal l) m=(subdiskMoment W a μ r m l).toReal := by
  have he := lintegral_coordinate Q (finiteAngleLaw W a l) (subdiskMass a μ r)
    (subdiskMass_measurable a ha μ hμ r) l (hQlaw l) (fun x=>x^m)
    (measurable_id.pow_const m)
  unfold moment sequenceLevelReal
  simp only [←ENNReal.toReal_pow]
  rw [integral_toReal ((measurable_pi_apply l).pow_const m).aemeasurable
    (hfin.mono (fun x hx=>ENNReal.pow_lt_top ((le_iSup x l).trans_lt hx))),he]
  rfl

 

theorem sequenceReal_moment_data (Q : Measure (ℕ→ℝ≥0∞)) [IsProbabilityMeasure Q]
    (hmono : ∀ᵐ x∂Q,Monotone x) (hfin : ∀ᵐ x∂Q,diskSequenceMass x<∞)
    (hmom : ∀m : ℕ, 1 ≤ m → 0<(∫⁻x,diskSequenceMass x^m∂Q) ∧
      (∫⁻x,diskSequenceMass x^m∂Q)<∞) :
    (∀ᵐ x∂Q,Monotone (fun l=>sequenceLevelReal l x) ∧
      Tendsto (fun l=>sequenceLevelReal l x) atTop (𝓝 (sequenceMassReal x))) ∧
    (∀m : ℕ,Integrable (fun x=>sequenceMassReal x^m) Q) ∧
    (∀m : ℕ, 1 ≤ m → 0 < moment Q sequenceMassReal m) ∧
    (∀m : ℕ,Monotone (fun l=>moment Q (sequenceLevelReal l) m) ∧
      Tendsto (fun l=>moment Q (sequenceLevelReal l) m) atTop
        (𝓝 (moment Q sequenceMassReal m))) := by
  have hp : ∀ᵐ x∂Q,Monotone (fun l=>sequenceLevelReal l x) ∧
      Tendsto (fun l=>sequenceLevelReal l x) atTop (𝓝 (sequenceMassReal x)) := by
    filter_upwards [hmono,hfin] with x hx hxf
    exact ⟨sequenceReal_monotone hx hxf,sequenceReal_tendsto hx hxf⟩
  have hI (m : ℕ) : Integrable (fun x=>sequenceMassReal x^m) Q := by
    rcases m with _|m
    · simpa only [pow_zero] using integrable_const (1:ℝ)
    · exact sequenceMassReal_integrable_pow Q (m+1) (hmom _ (by omega)).2
  refine ⟨hp,hI,?_,?_⟩
  · intro m hm
    rw [sequenceMassReal_moment Q hfin m]
    exact ENNReal.toReal_pos (hmom m hm).1.ne' (hmom m hm).2.ne
  · intro m
    exact (increasing_moments Q sequenceMassReal sequenceLevelReal sequenceLevelReal_measurable
      (Eventually.of_forall (fun x l=>sequenceLevelReal_nonneg l x))
      (hp.mono (fun _ hx=>hx.1)) (hp.mono (fun _ hx=>hx.2)) m (hI m)).2

end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions CompactSequence
open TraceMassIntegration TraceMassContinuity MomentBatches

 

structure CenteredMomentModel (κ a : ℝ) (ha : 1/4<a) (W : Measure GDriver) where
  supports : ℕ→Finset ℕ
  coeff : ℕ→ℕ→ℝ
  nonneg : ∀k j,j∈supports k → 0≤coeff k j
  tails : ∀k j,j∈supports k → k≤j
  normalized : ∀k,∑j∈supports k,coeff k j=1
  radiusIndex : ℕ
  law : Measure (ℕ→ℝ≥0∞)
  probability : IsProbabilityMeasure law
  finite_laws : ∀n,law.map (initialVector n)=(finiteAngleLaw W a n).map
    (fun p=>fun i : Fin (n+1)=>subdiskMass a (recoveredMass a ha supports coeff nonneg)
      (subdiskRadius radiusIndex) i p)
  increasing_finite : ∀ᵐ x∂law,Monotone x ∧ diskSequenceMass x<∞
  positive_moments : ∀m : ℕ, 1 ≤ m → 0<(∫⁻x,diskSequenceMass x^m∂law) ∧
    (∫⁻x,diskSequenceMass x^m∂law)<∞
  canonical : CanonicalMassData κ a ha W (recoveredMass a ha supports coeff nonneg)

 

theorem actual_centered_moment_model (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure TDriver) (hW : Target.IsWiener W) :
    Nonempty (CenteredMomentModel κ (Target.a κ) (a_gt_quarter hκ hκ8)
      (W.map driverHomeomorph)) := by
  obtain ⟨s,c,hc,hs,hsum,D,hreg,hμ,hraw,hpath,n₀,Q,hQ,hlaw,hseq,hmom⟩ :=
    actual_subdisk_positive_moments κ hκ hκ8 W hW
  exact ⟨{
    supports := s
    coeff := c
    nonneg := hc
    tails := hs
    normalized := hsum
    radiusIndex := n₀
    law := Q
    probability := hQ
    finite_laws := hlaw
    increasing_finite := hseq.mono (fun x hx=>⟨hx.1,hx.2.2⟩)
    positive_moments := fun m hm=>⟨(hmom m hm).1,(hmom m hm).2.1⟩
    canonical := D }⟩

namespace CenteredMomentModel
variable {κ a : ℝ} {ha : 1/4<a} {W : Measure GDriver} (M : CenteredMomentModel κ a ha W)

 

def gauge (d : ℝ) : ℝ→ℝ := fullMomentGauge M.law sequenceMassReal sequenceLevelReal a d

def mass : ℝ≥0∞→GDriver→Measure UpperPlane :=
  recoveredMass a ha M.supports M.coeff M.nonneg

lemma mass_measurable : Measurable (fun p : ℝ≥0∞×GDriver=>M.mass p.1 p.2) :=
  recoveredMass_joint_measurable a ha M.supports M.coeff M.nonneg

lemma integrable_moments (m : ℕ) : Integrable (fun x=>sequenceMassReal x^m) M.law := by
  let := M.probability
  exact (sequenceReal_moment_data M.law (M.increasing_finite.mono (fun _ hx=>hx.1))
    (M.increasing_finite.mono (fun _ hx=>hx.2)) M.positive_moments).2.1 m

lemma moments_positive (m : ℕ) (hm : 1 ≤ m) : 0 < moment M.law sequenceMassReal m := by
  let := M.probability
  exact (sequenceReal_moment_data M.law (M.increasing_finite.mono (fun _ hx=>hx.1))
    (M.increasing_finite.mono (fun _ hx=>hx.2)) M.positive_moments).2.2.1 m hm

lemma moment_finite_level (m l : ℕ) :
    moment M.law (sequenceLevelReal l) m=
      (subdiskMoment W a M.mass (subdiskRadius M.radiusIndex) m l).toReal := by
  let (v : ℝ≥0∞) (b : GDriver) : IsFiniteMeasureOnCompacts (M.mass v b) := M.canonical.finite_compact v b
  exact sequenceLevelReal_moment W a ha M.mass M.mass_measurable (subdiskRadius M.radiusIndex)
    M.law M.finite_laws (M.increasing_finite.mono (fun _ hx=>hx.2)) m l

lemma finite_moments_increasing (m : ℕ) : Monotone
    (fun l=>moment M.law (sequenceLevelReal l) m) := by
  let := M.probability
  exact ((sequenceReal_moment_data M.law (M.increasing_finite.mono (fun _ hx=>hx.1))
    (M.increasing_finite.mono (fun _ hx=>hx.2)) M.positive_moments).2.2.2 m).1

lemma finite_moments_tendsto (m : ℕ) :
    Tendsto (fun l=>moment M.law (sequenceLevelReal l) m) atTop
      (𝓝 (moment M.law sequenceMassReal m)) := by
  let := M.probability
  exact ((sequenceReal_moment_data M.law (M.increasing_finite.mono (fun _ hx=>hx.1))
    (M.increasing_finite.mono (fun _ hx=>hx.2)) M.positive_moments).2.2.2 m).2

lemma gauge_admissible {d : ℝ} (hd : 0<d) (hd2 : d≤2) : Target.IsHausdorffGauge (M.gauge d) := by
  let := M.probability
  exact (fullMomentGauge_properties M.law sequenceMassReal sequenceLevelReal
    (Eventually.of_forall sequenceMassReal_nonneg) M.integrable_moments
    (M.moments_positive 1 le_rfl) (by linarith : 0≤a) hd hd2).1

lemma gauge_doubling {d : ℝ} (hd : 0<d) (hd2 : d≤2) (C r : ℝ) (hC : 1≤C) (hr : 0≤r) :
    M.gauge d (C*r) ≤ C^2*M.gauge d r := by
  let := M.probability
  exact (fullMomentGauge_properties M.law sequenceMassReal sequenceLevelReal
    (Eventually.of_forall sequenceMassReal_nonneg) M.integrable_moments
    (M.moments_positive 1 le_rfl) (by linarith : 0≤a) hd hd2).2 C r hC hr

lemma selected_moments (n : ℕ) (hn : 0<n) :
    let l := momentLevel M.law sequenceMassReal sequenceLevelReal n
    0<l ∧ 3*moment M.law sequenceMassReal n/4 < moment M.law (sequenceLevelReal l) n := by
  let := M.probability
  obtain ⟨hp,hI,hm,hlim⟩ := sequenceReal_moment_data M.law
    (M.increasing_finite.mono (fun _ hx=>hx.1))
    (M.increasing_finite.mono (fun _ hx=>hx.2)) M.positive_moments
  have hh := selected_level_moment M.law sequenceMassReal sequenceLevelReal sequenceLevelReal_measurable
    (Eventually.of_forall (fun x l=>sequenceLevelReal_nonneg l x))
    (hp.mono (fun _ hx=>hx.1)) (hp.mono (fun _ hx=>hx.2)) hI (hm 1 le_rfl) n hn
  exact ⟨hh.1,hh.2.2⟩

 

lemma success (n : ℕ) (hn : 3≤n) :
    (2:ℝ)^n/8 ≤ ∑'k : ℤ,(multiplicity (moment M.law sequenceMassReal) n k:ℝ)*
      M.law.real {x | (2:ℝ)^k ≤ sequenceLevelReal
        (momentLevel M.law sequenceMassReal sequenceLevelReal n) x} := by
  let := M.probability
  obtain ⟨hp,hI,hm,hlim⟩ := sequenceReal_moment_data M.law
    (M.increasing_finite.mono (fun _ hx=>hx.1))
    (M.increasing_finite.mono (fun _ hx=>hx.2)) M.positive_moments
  have hh := success_selected_level M.law sequenceMassReal sequenceLevelReal sequenceLevelReal_measurable
    (Eventually.of_forall (fun x l=>sequenceLevelReal_nonneg l x))
    (hp.mono (fun _ hx=>hx.1)) (hp.mono (fun _ hx=>hx.2)) hI (hm 1 le_rfl) n hn
  exact hh.2.trans hh.1

 
lemma tails_summable : Summable (fun i : EntryIndex (moment M.law sequenceMassReal)=>
    M.law.real {x | 16*threshold (moment M.law sequenceMassReal) i ≤ sequenceMassReal x}) := by
  let := M.probability
  exact summable_entry_tails M.law sequenceMassReal sequenceMassReal_measurable
    (Eventually.of_forall sequenceMassReal_nonneg) M.integrable_moments (M.moments_positive 1 le_rfl)

end CenteredMomentModel
end SLEExactGauge.CenteredMoments
end
end

end OAI
