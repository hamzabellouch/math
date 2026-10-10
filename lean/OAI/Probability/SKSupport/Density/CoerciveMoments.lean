import Mathlib
import OAI.Probability.SKSupport.Diffusion.FiniteFeedback
import OAI.Probability.SKSupport.Regularity.PositiveRegularity
import OAI.Probability.SKSupport.Density.GaussianLogDensity

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat

def coerciveJetPolynomial (c A B C : ℝ) : ℝ := c^2*C^2-12*c^3*A*B^2+6*c^4*A^4

def quarticJetPolynomial (c A : ℝ) : ℝ := c^4*A^4

lemma quarticMoment_scaled {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (c x : ℝ) :
    quarticMoment (fun y => c*deriv f y) x=quarticJetPolynomial c (iteratedDeriv 2 f x) := by
  have hd := contDiff_infty_iff_deriv.mp hf |>.2
  have he := scaled_jet hd c 1 x
  simp only [iteratedDeriv_one] at he
  simp only [quarticMoment,certV,he,quarticJetPolynomial,iteratedDeriv_succ,iteratedDeriv_zero]
  ring

lemma coercivePolynomial_scaled {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (c x : ℝ) :
    coercivePolynomial (fun y => c*deriv f y) x=coerciveJetPolynomial c
      (iteratedDeriv 2 f x) (iteratedDeriv 3 f x) (iteratedDeriv 4 f x) := by
  have hd := contDiff_infty_iff_deriv.mp hf |>.2
  have he := scaled_jet hd c 1 x
  simp only [iteratedDeriv_one] at he
  simp only [coercivePolynomial,certV,certW,certZ,he,scaled_jet hd,
    coerciveJetPolynomial,iteratedDeriv_succ,iteratedDeriv_zero]
  ring

lemma quarticJetPolynomial_bound {c A D E : ℝ} (hc : |c| ≤ D) (hA : |A| ≤ E) :
    |quarticJetPolynomial c A| ≤ D^4*E^4 := by
  simp only [quarticJetPolynomial,abs_mul,abs_pow]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hc 4) (pow_le_pow_left₀ (abs_nonneg _) hA 4)
    (by positivity) (by positivity)

lemma coerciveJetPolynomial_bound {c A B C D E F G : ℝ}
    (hc : |c| ≤ D) (hA : |A| ≤ E) (hB : |B| ≤ F) (hC : |C| ≤ G) :
    |coerciveJetPolynomial c A B C| ≤ D^2*G^2+12*D^3*E*F^2+6*D^4*E^4 := by
  have hD : 0 ≤ D := (abs_nonneg _).trans hc
  have hE : 0 ≤ E := (abs_nonneg _).trans hA
  have hF : 0 ≤ F := (abs_nonneg _).trans hB
  have hG : 0 ≤ G := (abs_nonneg _).trans hC
  have h1 : |c^2*C^2| ≤ D^2*G^2 := by
    simp only [abs_mul,abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hc 2) (pow_le_pow_left₀ (abs_nonneg _) hC 2) (by positivity) (by positivity)
  have h2 : |12*c^3*A*B^2| ≤ 12*D^3*E*F^2 := by
    simp only [abs_mul,abs_pow,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 12)]
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hc 3) (by norm_num)) hA (abs_nonneg _) (by positivity))
      (pow_le_pow_left₀ (abs_nonneg _) hB 2) (by positivity) (by positivity)
  have h3 : |6*c^4*A^4| ≤ 6*D^4*E^4 := by
    simp only [abs_mul,abs_pow,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hc 4) (by norm_num))
      (pow_le_pow_left₀ (abs_nonneg _) hA 4) (by positivity) (by positivity)
  exact (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add h1 h2)) h3)

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat

def sampleIndex (n : ℕ) (t : Time) : ℕ := ⌊(t:ℝ)/(approxMesh n:ℝ)⌋₊

def sampleNNTime (n : ℕ) (t : Time) : ℝ≥0 := (sampleIndex n t:ℝ≥0)*approxMesh n

lemma sampleIndex_lt (n : ℕ) (t : Time) : sampleIndex n t < n+1 := by
  unfold sampleIndex
  rw [Nat.floor_lt (div_nonneg t.property.1 (approxMesh n).coe_nonneg),div_lt_iff₀ (by exact_mod_cast approxMesh_pos n),approxMesh_horizon]
  exact t.property.2

lemma sampleNNTime_le (n : ℕ) (t : Time) : (sampleNNTime n t:ℝ) ≤ t := by
  have hh := Nat.floor_le (div_nonneg t.property.1 (approxMesh n).coe_nonneg)
  rw [le_div_iff₀ (by exact_mod_cast approxMesh_pos n)] at hh
  exact hh

lemma sampleNNTime_lower (n : ℕ) (t : Time) : (t:ℝ)-(approxMesh n:ℝ) < sampleNNTime n t := by
  have hh := Nat.lt_floor_add_one ((t:ℝ)/(approxMesh n:ℝ))
  rw [div_lt_iff₀ (by exact_mod_cast approxMesh_pos n)] at hh
  change (t:ℝ)-(approxMesh n:ℝ) < (sampleIndex n t:ℝ)*(approxMesh n:ℝ)
  dsimp only [sampleIndex]
  nlinarith

def sampleTime (n : ℕ) (t : Time) : Time :=
  ⟨sampleNNTime n t,⟨(sampleNNTime n t).coe_nonneg,(sampleNNTime_le n t).trans_lt t.property.2⟩⟩

lemma sampleTime_limit (t : Time) : Tendsto (fun n => sampleTime n t) atTop (𝓝 t) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun n => (t:ℝ)-(approxMesh n:ℝ)) atTop (𝓝 (t:ℝ)) by
      simpa only [sub_zero] using tendsto_const_nhds.sub approxMesh_limit) tendsto_const_nhds
    (fun n => (sampleNNTime_lower n t).le) (fun n => sampleNNTime_le n t)

lemma sampleNNTime_limit (t : Time) : Tendsto (fun n => sampleNNTime n t) atTop (𝓝 (⟨t,t.property.1⟩:ℝ≥0)) := by
  apply tendsto_subtype_rng.mpr
  exact (continuous_subtype_val.tendsto t).comp (sampleTime_limit t)

lemma sampleIndex_pos_eventually (t : Time) (ht : 0 < (t:ℝ)) : ∀ᶠ n in atTop, 0 < sampleIndex n t := by
  filter_upwards [approxMesh_limit.eventually (gt_mem_nhds ht)] with n hn
  rw [sampleIndex,Nat.floor_pos,le_div_iff₀ (by exact_mod_cast approxMesh_pos n)]
  simpa only [one_mul] using hn.le

lemma positiveCoeff_sample_eq (γ : OrderParameter) (n : ℕ) (t : Time) :
    (positiveCoeff γ n (sampleIndex n t):ℝ)=γ.val (sampleTime n t)+(approxMesh n:ℝ) := by
  unfold positiveCoeff
  rw [min_eq_left (by have := sampleIndex_lt n t;omega),NNReal.coe_add,approxCoeff_eq γ n _ (sampleIndex_lt n t)]
  rfl

lemma positiveCoeff_sample_limit (γ : OrderParameter) (t : Time) (ht : ContinuousAt γ.val t) :
    Tendsto (fun n => (positiveCoeff γ n (sampleIndex n t):ℝ)) atTop (𝓝 (γ.val t)) := by
  simp_rw [positiveCoeff_sample_eq]
  simpa only [add_zero,Function.comp_apply] using (ht.tendsto.comp (sampleTime_limit t)).add approxMesh_limit

lemma positiveCoeff_sample_bound (γ : OrderParameter) (n : ℕ) (t : Time) :
    (positiveCoeff γ n (sampleIndex n t):ℝ) ≤ γ.val t+1 := by
  rw [positiveCoeff_sample_eq]
  apply add_le_add (γ.monotone (sampleNNTime_le n t))
  unfold approxMesh
  simp only [NNReal.coe_inv,NNReal.coe_natCast]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

lemma positiveValue_sample (γ : OrderParameter) (n : ℕ) (t : Time) :
    positiveValue γ n (sampleTime n t)=backwardBoundary (positiveCoeff γ n) (approxMesh n)
      (softAbs (positiveTerminal γ n)) (n+1) (sampleIndex n t) := by
  have hf := regularDatum_softAbs (ne_of_gt (positiveTerminal_pos γ n))
  have hLip := softAbs_lipschitz (ne_of_gt (positiveTerminal_pos γ n))
  have hh := finiteValue_shift hf hLip (positiveCoeff γ n) (approxMesh n)
    ((sampleIndex_lt n t).le) 0 (le_refl (0:ℝ))
  simp only [add_zero,Nat.zero_add,finiteValue_zero hf hLip] at hh
  exact hh

end ZeroTemperatureSK

end
end

end OAI
