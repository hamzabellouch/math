import OAI.Dynamics.StandardMap.CriticalScales

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Filter Set
open scoped Topology Classical
namespace StandardMapEntropy
lemma doublingConstant_ge_one : 1 ≤ doublingConstant := by
  unfold doublingConstant
  linarith [cancellationConstant_pos]

def BadGrowth (η k : ℝ) : Prop := ∃ n : ℕ, 0<n ∧ η ≤ meanDeficit k n
lemma badGrowth_arbitrarily_large (η : ℝ)
    (hbad : ¬ ∃ K : ℝ, ∀ k : ℝ, K≤k → ∀ n : ℕ, 0<n → meanDeficit k n < η) :
    ∀ K : ℝ, ∃ k : ℝ, K≤k ∧ BadGrowth η k := by
  push Not at hbad
  exact hbad

lemma choose_critical_parameter (η θ : ℝ) (hη : 0<η) (hθ : 0<θ) (hθ1 : θ<1)
    (hθη : θ<η/2) (p : ℕ) (R : ℝ)
    (hbad : ∀ K : ℝ, ∃ k : ℝ, K≤k ∧ BadGrowth η k) :
    ∃ k : ℝ, ∃ q : ℕ, 0<k ∧ R≤k ∧ p<q ∧ meanDeficit k (2^p)≤θ^2 ∧
      θ < meanDeficit k (2^q) ∧ meanDeficit k (2^q)≤doublingConstant*θ+doublingConstant/((2^p:ℕ):ℝ) ∧
      (∀ m : ℕ, meanDeficit k (2^(p+m))≤(2*doublingConstant)^m*(θ^2+1/((2^p:ℕ):ℝ))) ∧
      (∀ m : ℕ, meanDeficit k (2^(q+m))≤(2*doublingConstant)^m*(meanDeficit k (2^q)+1/((2^p:ℕ):ℝ))) := by
  obtain ⟨M₀,hM₀⟩ := eventually_meanDeficit_doubling
  obtain ⟨M₁,hM₁⟩ := meanDeficit_fixed_small (2^p) (by positivity) (θ^2) (sq_pos_of_pos hθ)
  let A := max M₀ M₁
  obtain ⟨k,hk,hbadk⟩ := hbad (max (max R 1) ((A-4)/(2*Real.pi)))
  have hk0 : 0<k := lt_of_lt_of_le (by norm_num) ((le_max_right R 1).trans ((le_max_left _ _).trans hk))
  have hkR : R≤k := (le_max_left R 1).trans ((le_max_left _ _).trans hk)
  have hKA : A≤growthBase k := by
    have hh := (le_max_right (max R 1) ((A-4)/(2*Real.pi))).trans hk
    have hpi : 0<2*Real.pi := by positivity
    have he := (div_le_iff₀ hpi).mp hh
    unfold growthBase
    nlinarith
  have hsmall := hM₁ k hk0.le ((le_max_right M₀ M₁).trans hKA)
  have hdouble := fun n hn => (hM₀ k hk0 ((le_max_left M₀ M₁).trans hKA) n hn).2
  have hex : ∃ q : ℕ, θ < meanDeficit k (2^q) := by
    obtain ⟨q,hq⟩ := positive_deficit_dyadic k η hk0.le hη hbadk
    exact ⟨q,hθη.trans hq⟩
  obtain ⟨q,hpq,hq,hup,hlo,hhi⟩ := critical_scale_finite k doublingConstant θ hk0.le doublingConstant_ge_one hdouble p hsmall hθ hθ1 hex
  exact ⟨k,q,hk0,hkR,hpq,hsmall,hq,hup,hlo,hhi⟩

noncomputable def criticalTheta (r i : ℕ) : ℝ := (1/2:ℝ)^(i+r+1)
def criticalLowerExponent (r i : ℕ) : ℕ := 2*(i+r+1)
lemma criticalTheta_pos (r i : ℕ) : 0 < criticalTheta r i := by unfold criticalTheta; positivity
lemma criticalTheta_lt_one (r i : ℕ) : criticalTheta r i < 1 := by
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
lemma criticalTheta_square (r i : ℕ) :
    1/((2^(criticalLowerExponent r i):ℕ):ℝ)=(criticalTheta r i)^2 := by
  unfold criticalLowerExponent criticalTheta
  push_cast
  simp only [div_pow,one_pow,← pow_mul]
  rw [Nat.mul_comm 2]
lemma criticalTheta_tendsto (r : ℕ) : Tendsto (criticalTheta r) atTop (𝓝 0) := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have he (i : ℕ) : criticalTheta r i=(1/2:ℝ)^i*(1/2:ℝ)^(r+1) := by
    unfold criticalTheta
    rw [← pow_add]
    congr 1
  have heq : criticalTheta r=(fun i => (1/2:ℝ)^i*(1/2:ℝ)^(r+1)) := funext he
  rw [heq]
  simpa only [zero_mul] using ht.mul_const ((1/2:ℝ)^(r+1))
structure CriticalScaleSequence where
  offset : ℕ
  parameter : ℕ → ℝ
  exponent : ℕ → ℕ
  positive : ∀ i, 0 < parameter i
  large : ∀ i : ℕ, (i:ℝ) ≤ parameter i
  lower_lt : ∀ i, criticalLowerExponent offset i < exponent i
  threshold : ∀ i, criticalTheta offset i < meanDeficit (parameter i) (2^(exponent i))
  upper : ∀ i, meanDeficit (parameter i) (2^(exponent i)) ≤ 2*doublingConstant*criticalTheta offset i
  initial : ∀ i m, meanDeficit (parameter i) (2^(criticalLowerExponent offset i+m)) ≤
    2*(2*doublingConstant)^m*(criticalTheta offset i)^2
  terminal : ∀ i m, meanDeficit (parameter i) (2^(exponent i+m)) ≤
    2*(2*doublingConstant)^m*meanDeficit (parameter i) (2^(exponent i))
lemma exists_critical_scale_sequence (η : ℝ) (hη : 0<η)
    (hbad : ∀ K : ℝ, ∃ k : ℝ, K≤k ∧ BadGrowth η k) : Nonempty CriticalScaleSequence := by
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one (show 0<η/2 by positivity) (by norm_num : (1/2:ℝ)<1)
  have htη (i : ℕ) : criticalTheta r i < η/2 := by
    apply lt_of_le_of_lt _ hr
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hx (i : ℕ) := choose_critical_parameter η (criticalTheta r i) hη (criticalTheta_pos r i)
    (criticalTheta_lt_one r i) (htη i) (criticalLowerExponent r i) (i:ℝ) hbad
  choose k q hk hkR hpq hsmall hq hqU hlo hhi using hx
  refine ⟨⟨r,k,q,hk,hkR,hpq,hq,?_,?_,?_⟩⟩
  · intro i
    have hh := hqU i
    rw [show doublingConstant/((2^(criticalLowerExponent r i):ℕ):ℝ)=
      doublingConstant*(1/((2^(criticalLowerExponent r i):ℕ):ℝ)) by ring,criticalTheta_square] at hh
    have ht := criticalTheta_pos r i
    have ht1 := criticalTheta_lt_one r i
    have hmul := mul_le_mul_of_nonneg_left (show (criticalTheta r i)^2 ≤ criticalTheta r i by nlinarith) doublingConstant_pos.le
    nlinarith
  · intro i m
    have hh := hlo i m
    rw [criticalTheta_square] at hh
    nlinarith
  · intro i m
    have hh := hhi i m
    rw [criticalTheta_square] at hh
    have ht := criticalTheta_pos r i
    have ht1 := criticalTheta_lt_one r i
    have ht2 : (criticalTheta r i)^2 ≤ meanDeficit (k i) (2^(q i)) := by nlinarith [hq i]
    have hp : 0 ≤ (2*doublingConstant)^m := pow_nonneg (mul_nonneg (by norm_num) doublingConstant_pos.le) _
    nlinarith [mul_le_mul_of_nonneg_left ht2 hp]
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence)
noncomputable def epsilon (i : ℕ) : ℝ := meanDeficit (S.parameter i) (2^(S.exponent i))
lemma epsilon_pos (i : ℕ) : 0 < S.epsilon i := (criticalTheta_pos S.offset i).trans (S.threshold i)
lemma epsilon_tendsto : Tendsto S.epsilon atTop (𝓝 0) := by
  apply squeeze_zero (fun i => (S.epsilon_pos i).le) S.upper
  simpa using (criticalTheta_tendsto S.offset).const_mul (2*doublingConstant)
lemma parameter_tendsto : Tendsto S.parameter atTop atTop :=
  tendsto_atTop_mono S.large tendsto_natCast_atTop_atTop
lemma initial_ratio_bound (i m : ℕ) :
    meanDeficit (S.parameter i) (2^(criticalLowerExponent S.offset i+m))/S.epsilon i ≤
      2*(2*doublingConstant)^m*criticalTheta S.offset i := by
  apply (div_le_iff₀ (S.epsilon_pos i)).mpr
  have hh := S.initial i m
  have ht := (S.threshold i).le
  change criticalTheta S.offset i ≤ S.epsilon i at ht
  have ht0 := criticalTheta_pos S.offset i
  have hc := doublingConstant_pos
  have hp : 0 ≤ 2*(2*doublingConstant)^m*criticalTheta S.offset i := by positivity
  nlinarith [mul_le_mul_of_nonneg_left ht hp]
lemma initial_ratio_tendsto (m : ℕ) :
    Tendsto (fun i => meanDeficit (S.parameter i) (2^(criticalLowerExponent S.offset i+m))/S.epsilon i) atTop (𝓝 0) := by
  apply squeeze_zero (fun i => div_nonneg ((meanDeficit_bounds _ (S.positive i).le _ (by positivity)).1) (S.epsilon_pos i).le)
    (fun i => S.initial_ratio_bound i m)
  simpa using (criticalTheta_tendsto S.offset).const_mul (2*(2*doublingConstant)^m)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
