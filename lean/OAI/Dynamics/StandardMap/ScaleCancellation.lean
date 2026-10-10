import OAI.Dynamics.StandardMap.BridgePattern

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def arrayCancellation (s t : DyadicTime) (d : DistanceArray) : Prop :=
  (1-1/100000000:ℝ)*((t:ℝ)-(s:ℝ))/2<d.val s (dyadicMid s t) ∧
  (1-1/100000000:ℝ)*((t:ℝ)-(s:ℝ))/2<d.val (dyadicMid s t) t ∧
  d.val s t<(1/100000000:ℝ)*((t:ℝ)-(s:ℝ))/2
lemma isOpen_arrayCancellation (s t : DyadicTime) : IsOpen {d | arrayCancellation s t d} :=
  (isOpen_lt continuous_const (continuous_arrayEval s (dyadicMid s t))).inter
    ((isOpen_lt continuous_const (continuous_arrayEval (dyadicMid s t) t)).inter
      (isOpen_lt (continuous_arrayEval s t) continuous_const))
lemma sample_cancellation (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ))
    (he : arrayCancellation s t (sampleArray k hk z n hn)) :
    torusCancellation k m (torusIter k (a+(m:ℤ)) z) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hmid : (n:ℝ)*(dyadicMid s t:ℝ)=((a+(m:ℤ):ℤ):ℝ) := by
    rw [dyadicMid_val]; push_cast; nlinarith
  have ht' : (n:ℝ)*(t:ℝ)=((a+(m:ℤ)+(m:ℤ):ℤ):ℝ) := by push_cast; linarith
  change _<rescaledDistance k z n s (dyadicMid s t) ∧
    _<rescaledDistance k z n (dyadicMid s t) t ∧ rescaledDistance k z n s t<_ at he
  rw [rescaledDistance_aligned _ _ _ _ _ _ _ hs hmid,
    rescaledDistance_aligned _ _ _ _ _ _ _ hmid ht',
    rescaledDistance_aligned _ _ _ _ _ _ _ hs ht'] at he
  rw [torusCancellation_iff_distance k hk]
  simp only [productDistance_shift,zero_add]
  rw [show -(m:ℤ)+(a+(m:ℤ))=a by ring,show (m:ℤ)+(a+(m:ℤ))=a+(m:ℤ)+(m:ℤ) by ring,
    productDistance_symm k z (a+(m:ℤ)) a]
  have h1 := (lt_div_iff₀ hnR).mp he.1
  have h2 := (lt_div_iff₀ hnR).mp he.2.1
  have h3 := (div_lt_iff₀ hnR).mp he.2.2
  have heq : ((t:ℝ)-(s:ℝ))*(n:ℝ)=2*(m:ℝ) := by nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith
lemma quarter_pow_le_inv (m : ℕ) (hm : 0 < m) : (1/4:ℝ)^m ≤ 1/(m:ℝ) := by
  have hpow : (m:ℝ) ≤ (4:ℝ)^m := by
    have hh : (m:ℝ) ≤ (2:ℝ)^m := by exact_mod_cast nat_le_two_power m
    exact hh.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) m)
  have he : (4:ℝ)^m*(1/4:ℝ)^m=1 := by rw [←mul_pow]; norm_num
  apply (le_div_iff₀ (by exact_mod_cast hm : (0:ℝ)< m)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hpow (show 0≤(1/4:ℝ)^m by positivity)]
lemma integral_le_event_bound {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hi : Integrable f μ) (B : ℝ) (_hB : 0≤B) (hfb : ∀ x,f x≤B)
    (E : Set X) (hE : MeasurableSet E) (hz : ∀ x∉E,f x=0) :
    (∫ x,f x ∂μ) ≤ B*(μ E).toReal := by
  have hdom : ∀ x,f x≤E.indicator (fun _ => B) x := by
    intro x
    by_cases hx : x∈E
    · simpa only [indicator_of_mem hx] using hfb x
    · simp only [indicator_of_notMem hx,hz x hx,le_refl]
  have hh := integral_mono hi ((integrable_const B).indicator hE) hdom
  rw [integral_indicator hE,integral_const,smul_eq_mul] at hh
  simpa only [Measure.real,Measure.restrict_apply_univ,mul_comm] using hh
lemma integral_sample_cancellation_bound (k : ℝ) (hk : 0≤k)
    (C : ℝ) (hC : 0≤C) (hc : ∀ m : ℕ,area {z | torusCancellation k m z}≤ENNReal.ofReal (C*(1/4:ℝ)^m))
    (n : ℕ) (hn : 0<n) (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ))
    (F : DistanceArray → ℝ) (hF : Continuous F) (B : ℝ) (hB : 0≤B) (hFB : ∀ d,F d≤B)
    (hz : ∀ d,¬arrayCancellation s t d → F d=0) :
    (∫ d,F d ∂sampleLaw k hk n hn) ≤ B*C/(m:ℝ) := by
  rw [integral_sampleLaw k hk n hn F hF]
  let E : Set Torus := {z | torusCancellation k m (torusIter k (a+(m:ℤ)) z)}
  have hE : MeasurableSet E := (isClosed_torusCancellation k m).measurableSet.preimage
    (continuous_torusIter k _).measurable
  have hzero : ∀ z∉E,F (sampleArray k hk z n hn)=0 := by
    intro z hz'
    apply hz
    intro hh
    exact hz' (sample_cancellation k hk z n hn s t a m hs ht hh)
  have hbound := integral_le_event_bound area _
    ((hF.comp (continuous_sampleArray k hk n hn)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    B hB (fun z => hFB _) E hE hzero
  have hme : area E=area {z | torusCancellation k m z} :=
    (measurePreserving_torusIter k _).measure_preimage (isClosed_torusCancellation k m).measurableSet.nullMeasurableSet
  rw [hme] at hbound
  have he := ENNReal.toReal_mono (by finiteness) (hc m)
  rw [ENNReal.toReal_ofReal (by positivity)] at he
  have hh := mul_le_mul_of_nonneg_left he hB
  have hpow := mul_le_mul_of_nonneg_left (quarter_pow_le_inv m hm) (mul_nonneg hB hC)
  calc
    _ ≤ _ := hbound
    _ ≤ B*(C*(1/4:ℝ)^m) := hh
    _ ≤ B*C/(m:ℝ) := by simpa only [mul_assoc,div_eq_mul_inv,one_mul] using hpow
lemma sum_scaled_inverse (m l : ℕ) (hm : 0 < m) :
    (∑ j∈Finset.range l,1/((m*2^j:ℕ):ℝ)) ≤ 2/(m:ℝ) := by
  have he (j : ℕ) : 1/((m*2^j:ℕ):ℝ)=(1/(m:ℝ))*(1/2:ℝ)^j := by push_cast; rw [div_pow]; ring
  simp_rw [he]
  rw [←Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (sum_geometric_two_le l) (by positivity : 0≤1/(m:ℝ))
  norm_num only [one_div] at *
  simpa only [mul_comm,div_eq_mul_inv] using hh
lemma integral_scale_cancellation_bound (k : ℝ) (hk : 0≤k)
    (C : ℝ) (hC : 0≤C) (hc : ∀ m : ℕ,area {z | torusCancellation k m z}≤ENNReal.ofReal (C*(1/4:ℝ)^m))
    (p l : ℕ) (ε : ℝ) (hε : 0<ε) (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)) (ht : ((2^p:ℕ):ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ))
    (F : DistanceArray → ℝ) (hF : Continuous F) (B : ℝ) (hB : 0≤B) (hFB : ∀ d,F d≤B)
    (hz : ∀ d,¬arrayCancellation s t d → F d=0) :
    (∫ d,F d ∂scaleLaw k hk p l ε) ≤ 2*B*C/((m:ℝ)*ε) := by
  rw [integral_scaleLaw k hk p l ε hε F hF]
  apply (div_le_iff₀ hε).mpr
  have hsum : (∑ j∈Finset.range l,∫ d,F d ∂sampleLaw k hk (2^(p+j)) (by positivity)) ≤
      B*C*∑ j∈Finset.range l,1/((m*2^j:ℕ):ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hs',ht'⟩ := aligned_times_scale p j s t a m hs ht
    simpa only [div_eq_mul_inv,one_mul] using integral_sample_cancellation_bound k hk C hC hc _ (by positivity)
      s t _ _ (by positivity) hs' ht' F hF B hB hFB hz
  have hh := hsum.trans (mul_le_mul_of_nonneg_left (sum_scaled_inverse m l hm) (mul_nonneg hB hC))
  apply hh.trans_eq
  field_simp
end StandardMapEntropy

end OAI
