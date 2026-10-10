import OAI.Dynamics.StandardMap.ClippedTests

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma inverse_scale_epsilon_bound (i p : ℕ) (hp : criticalLowerExponent S.offset i ≤ p) :
    1/(((2^p:ℕ):ℝ)*S.epsilon i) ≤ criticalTheta S.offset i := by
  have hpow : (1:ℝ)/((2^p:ℕ):ℝ) ≤ 1/((2^(criticalLowerExponent S.offset i):ℕ):ℝ) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hp
  rw [criticalTheta_square] at hpow
  rw [←div_div]
  apply (div_le_iff₀ (S.epsilon_pos i)).mpr
  have ht : criticalTheta S.offset i ≤ S.epsilon i := (S.threshold i).le
  exact hpow.trans (by nlinarith [mul_le_mul_of_nonneg_left ht (criticalTheta_pos S.offset i).le])
lemma cancellation_integral_tendsto (p l : ℕ → ℕ)
    (hp : ∀ i, criticalLowerExponent S.offset i ≤ p i)
    (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ))
    (F : DistanceArray → ℝ) (hF : Continuous F) (hF0 : ∀ d,0≤F d)
    (B : ℝ) (hB : 0≤B) (hFB : ∀ d,F d≤B)
    (hz : ∀ d,¬arrayCancellation s t d → F d=0) :
    Tendsto (fun i => ∫ d,F d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (l i) (S.epsilon i)) atTop (𝓝 0) := by
  obtain ⟨p₀,hp₀⟩ := dyadic_interval_aligned_eventually s t hst
  obtain ⟨M₀,hM₀⟩ := eventually_cancellation_area
  have hM : ∀ᶠ i in atTop,M₀≤growthBase (S.parameter i) :=
    (tendsto_growthBase.comp S.parameter_tendsto).eventually_ge_atTop M₀
  have hp' : Tendsto p atTop atTop := tendsto_atTop_mono hp S.lowerExponent_tendsto
  apply squeeze_zero' (Eventually.of_forall (fun i => integral_nonneg hF0))
  · filter_upwards [hp'.eventually_ge_atTop p₀,hM] with i hi hMi
    obtain ⟨a,m,hm,hs,ht⟩ := hp₀ _ hi
    have hb := integral_scale_cancellation_bound (S.parameter i) (S.positive i).le cancellationConstant
      cancellationConstant_pos.le (hM₀ _ (S.positive i) hMi) (p i) (l i) (S.epsilon i) (S.epsilon_pos i)
      s t a m hm hs ht F hF B hB hFB hz
    have hlen : ((2^(p i):ℕ):ℝ)*((t:ℝ)-(s:ℝ))=2*(m:ℝ) := by nlinarith
    have he : 2*B*cancellationConstant/((m:ℝ)*S.epsilon i)=
        (4*B*cancellationConstant/((t:ℝ)-(s:ℝ)))*(1/(((2^(p i):ℕ):ℝ)*S.epsilon i)) := by
      have hmR : (m:ℝ)=((2^(p i):ℕ):ℝ)*((t:ℝ)-(s:ℝ))/2 := by linarith
      rw [hmR]
      field_simp
      ring
    exact hb.trans (he.le.trans (mul_le_mul_of_nonneg_left (S.inverse_scale_epsilon_bound i _ (hp i))
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) cancellationConstant_pos.le) (sub_pos.mpr hst).le)))
  · simpa only [mul_zero] using (criticalTheta_tendsto S.offset).const_mul (4*B*cancellationConstant/((t:ℝ)-(s:ℝ)))
lemma cancellation_vague_tendsto (p l : ℕ → ℕ)
    (hp : ∀ i, criticalLowerExponent S.offset i ≤ p i)
    (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) (g : C_c(NonAffineArray,ℝ))
    (hg : ∀ d,0≤g d) (hz : ∀ d : NonAffineArray,¬arrayCancellation s t d.val → g d=0) :
    Tendsto (fun i => ∫ d,g d ∂nonaffinePart (scaleLaw (S.parameter i) (S.positive i).le (p i) (l i) (S.epsilon i))) atTop (𝓝 0) := by
  let F := arrayTestExtend g
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn F.continuous.continuousOn
  have hF0 : ∀ d,0≤F d := by
    intro d
    by_cases hd : d∈affineLocus
    · rw [show F d=0 from arrayTestExtend_affine g d hd]
    · exact (arrayTestExtend_apply g ⟨d,hd⟩).symm ▸ hg ⟨d,hd⟩
  have hFB : ∀ d,F d≤ max B 0 := by
    intro d
    have hdb : |F d| ≤ B := by convert! hB d (mem_univ d) using 1
    exact (le_abs_self _).trans (hdb.trans (le_max_left _ _))
  have hFz : ∀ d,¬arrayCancellation s t d → F d=0 := by
    intro d hd
    by_cases ha : d∈affineLocus
    · exact arrayTestExtend_affine g d ha
    · exact (arrayTestExtend_apply g ⟨d,ha⟩).trans (hz ⟨d,ha⟩ hd)
  have hh := S.cancellation_integral_tendsto p l hp s t hst F F.continuous hF0 (max B 0) (le_max_right _ _) hFB hFz
  simpa only [F,integral_arrayTestExtend] using hh
lemma cancellation_null_multi (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) :
    L.multi {d | arrayCancellation s t d.val}=0 := by
  apply vague_open_null L.filter (fun i => nonaffinePart (S.multiLaw i)) L.multi L.multi_converges
    ((isOpen_arrayCancellation s t).preimage continuous_subtype_val)
  intro g hg hz
  exact (S.cancellation_vague_tendsto (criticalLowerExponent S.offset)
    (fun i => S.exponent i-criticalLowerExponent S.offset i) (fun i => le_rfl) s t hst g hg hz).mono_left L.refines
lemma cancellation_null_terminal (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) :
    L.terminal {d | arrayCancellation s t d.val}=0 := by
  apply vague_open_null L.filter (fun i => nonaffinePart (S.terminalLaw i)) L.terminal L.terminal_converges
    ((isOpen_arrayCancellation s t).preimage continuous_subtype_val)
  intro g hg hz
  exact (S.cancellation_vague_tendsto S.exponent (fun _ => 1) (fun i => (S.lower_lt i).le) s t hst g hg hz).mono_left L.refines
end CriticalScaleSequence
end StandardMapEntropy

end OAI
