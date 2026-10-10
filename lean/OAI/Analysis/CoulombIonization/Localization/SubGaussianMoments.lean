import Mathlib

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SubGaussianMoments_scope

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal BigOperators

lemma even_pow_le_factorial_exp (x : ℝ) (k : ℕ) :
    x ^ (2 * k) ≤ (Nat.factorial (2 * k) : ℝ) * (Real.exp x + Real.exp (-x)) := by
  have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) (2 * k)
  have hab : |x| ^ (2 * k) = x ^ (2 * k) := by rw [pow_mul, pow_mul, sq_abs]
  rw [hab] at h
  have hf : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by positivity
  have he : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-x)]
    · rw [abs_of_nonpos hx]; linarith [Real.exp_pos x]
  exact (div_le_iff₀ hf).mp (h.trans he) |>.trans_eq (mul_comm _ _)

lemma subGaussian_even_moment_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (h : HasSubgaussianMGF X v μ) {k : ℕ} (hk : 0 < k) :
    Integrable (fun sample => X sample ^ (2 * k)) μ := by
  have hm : MemLp X (2 * k : ℕ) μ := by
    simpa only [NNReal.coe_natCast, ENNReal.coe_natCast] using h.memLp (2 * k : ℕ)
  have hi := hm.integrable_norm_pow (Nat.ne_of_gt (Nat.mul_pos (by norm_num) hk))
  simpa only [Real.norm_eq_abs, pow_mul, sq_abs] using hi

theorem subGaussian_even_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (h : HasSubgaussianMGF X v μ) {k : ℕ} (hk : 0 < k) :
    (∫ sample, X sample ^ (2 * k) ∂μ) ≤ (8 * Real.exp 1 * k * (v : ℝ)) ^ k := by
  by_cases hv : v = 0
  · subst v
    have he := h.ae_eq_zero_of_hasSubgaussianMGF_zero
    have hz : (∫ sample, X sample ^ (2 * k) ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [he] with sample hω
      simp [hω, Nat.ne_of_gt hk]
    simp [hz, Nat.ne_of_gt hk]
  have hvp : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
  let t : ℝ := Real.sqrt ((k : ℝ) / v)
  have ht : 0 < t := Real.sqrt_pos.2 (div_pos hkp hvp)
  have ht2 : t ^ 2 = (k : ℝ) / v := Real.sq_sqrt (div_pos hkp hvp).le
  have he : (v : ℝ) * t ^ 2 / 2 ≤ k := by rw [ht2]; field_simp; nlinarith
  have hexp : Real.exp ((v : ℝ) * t ^ 2 / 2) ≤ Real.exp (1 : ℝ) ^ k := by
    rw [← Real.exp_nat_mul]
    simpa using Real.exp_le_exp.mpr he
  have hi := subGaussian_even_moment_integrable h hk
  have hpoint := integral_mono (hi.const_mul (t ^ (2 * k)))
    (((h.integrable_exp_mul t).add (h.integrable_exp_mul (-t))).const_mul
      (Nat.factorial (2*k) : ℝ))
    (fun sample => by simpa only [Pi.add_apply, mul_pow, neg_mul] using even_pow_le_factorial_exp (t * X sample) k)
  simp only [Pi.add_apply] at hpoint
  rw [integral_const_mul, integral_const_mul, integral_add
    (h.integrable_exp_mul t) (h.integrable_exp_mul (-t))] at hpoint
  have hm1 : (∫ sample, Real.exp (t * X sample) ∂μ) ≤ Real.exp 1 ^ k :=
    (h.mgf_le t).trans hexp
  have hm2 : (∫ sample, Real.exp (-t * X sample) ∂μ) ≤ Real.exp 1 ^ k := by
    have hh := h.mgf_le (-t)
    simp only [neg_sq] at hh
    exact hh.trans hexp
  have hfact : (Nat.factorial (2*k) : ℝ) ≤ ((2*k : ℕ) : ℝ) ^ (2*k) := by
    exact_mod_cast Nat.factorial_le_pow (2*k)
  have hb : t ^ (2*k) * (∫ sample, X sample ^ (2*k) ∂μ) ≤
      ((2*k : ℕ) : ℝ) ^ (2*k) * (2 * Real.exp 1 ^ k) := by
    calc
      _ ≤ (Nat.factorial (2*k) : ℝ) * (2 * Real.exp 1 ^ k) :=
        hpoint.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      _ ≤ _ := mul_le_mul_of_nonneg_right hfact (by positivity)
  have htwo : (2 : ℝ) ≤ 2 ^ k := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.succ_le_iff.mpr hk)
  have hb' : t ^ (2*k) * (∫ sample, X sample ^ (2*k) ∂μ) ≤
      ((8 * Real.exp 1 * k) : ℝ) ^ k * (k : ℝ) ^ k := by
    calc
      _ ≤ ((2*k : ℕ) : ℝ) ^ (2*k) * (2 * Real.exp 1 ^ k) := hb
      _ ≤ ((2*k : ℕ) : ℝ) ^ (2*k) * (2 ^ k * Real.exp 1 ^ k) := by
        gcongr
      _ = _ := by
        push_cast
        rw [pow_mul]
        ring_nf
        rw [show (8 : ℝ) = 2 * 4 by norm_num, mul_pow]
        ring
  have htPow : t ^ (2*k) = ((k : ℝ) / v) ^ k := by rw [pow_mul, ht2]
  rw [htPow] at hb'
  apply (mul_le_mul_iff_right₀ (pow_pos (div_pos hkp hvp) k)).mp
  calc
    _ ≤ ((8 * Real.exp 1 * k) : ℝ) ^ k * (k : ℝ) ^ k := hb'
    _ = _ := by rw [← mul_pow, ← mul_pow]; congr 1; field_simp

end Work_SubGaussianMoments_scope

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal BigOperators

def observationSign (b : Bool) : ℝ := if b then 1 else -1

def signLaw : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance signLaw_probability : IsProbabilityMeasure signLaw := by
  unfold signLaw
  infer_instance

lemma observationSign_subGaussian : HasSubgaussianMGF observationSign 1 signLaw := by
  have hm : AEMeasurable observationSign signLaw := Measurable.of_discrete.aemeasurable
  have hb : ∀ᵐ b ∂signLaw, observationSign b ∈ Set.Icc (-1) 1 := by
    filter_upwards [] with b
    cases b <;> norm_num [observationSign]
  have hz : (∫ b, observationSign b ∂signLaw) = 0 := by
    rw [signLaw, PMF.integral_eq_sum]
    norm_num [observationSign, Fintype.sum_bool]
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hz
  norm_num at h
  exact h

def signProduct (ι : Type*) [Fintype ι] : Measure (ι → Bool) :=
  Measure.pi (fun _ : ι => signLaw)

instance signProduct_probability (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (signProduct ι) := by
  unfold signProduct
  infer_instance

lemma observationSign_eval_subGaussian {ι : Type*} [Fintype ι] (i : ι) :
    HasSubgaussianMGF (fun ε : ι → Bool => observationSign (ε i)) 1 (signProduct ι) := by
  have hm : AEMeasurable (fun ε : ι → Bool => ε i) (signProduct ι) :=
    (measurable_pi_apply i).aemeasurable
  have hmap : (signProduct ι).map (fun ε => ε i) = signLaw :=
    (measurePreserving_eval (fun _ : ι => signLaw) i).map_eq
  have h : HasSubgaussianMGF observationSign 1
      ((signProduct ι).map (fun ε => ε i)) := hmap ▸ observationSign_subGaussian
  exact HasSubgaussianMGF.of_map hm h

lemma sign_sum_subGaussian {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    HasSubgaussianMGF (fun ε : ι → Bool => ∑ i, a i * observationSign (ε i))
      (∑ i, (NNReal.mk (a i ^ 2) (sq_nonneg (a i)))) (signProduct ι) := by
  have hind : iIndepFun (fun i (ε : ι → Bool) => a i * observationSign (ε i))
      (signProduct ι) := by
    exact iIndepFun_pi (μ := fun _ : ι => signLaw)
      (X := fun i b => a i * observationSign b)
      (fun i => Measurable.of_discrete.aemeasurable)
  apply HasSubgaussianMGF.sum_of_iIndepFun hind
  intro i _
  have h := (observationSign_eval_subGaussian i).const_mul (a i)
  change HasSubgaussianMGF _ (NNReal.mk (a i ^ 2) (sq_nonneg (a i)) * 1) _ at h
  simpa only [mul_one] using h

theorem sign_sum_even_moment_le {ι : Type*} [Fintype ι] (a : ι → ℝ)
    {k : ℕ} (hk : 0 < k) :
    (∫ ε, (∑ i, a i * observationSign (ε i)) ^ (2*k) ∂signProduct ι) ≤
      (8 * Real.exp 1 * k * (∑ i, a i ^ 2)) ^ k := by
  have h := subGaussian_even_moment_le (sign_sum_subGaussian a) hk
  have hc : (↑(∑ i, NNReal.mk (a i ^ 2) (sq_nonneg (a i))) : ℝ) =
      ∑ i, a i ^ 2 := by simp
  rw [hc] at h
  exact h

end CoulombObservation

end

end OAI
