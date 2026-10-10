import Mathlib
import OAI.Probability.SKRatio.Matrices.GaussianProductIntegral
import OAI.Probability.SKRatio.Entropy.Partition

namespace OAI

section
noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def standardSample (β : ℝ) (n : ℕ) (z : Edge n → ℝ) : Disorder n :=
  fun e => sqrt (β^2/n)*z e

lemma standardSample_continuous (β : ℝ) (n : ℕ) : Continuous (standardSample β n) := by
  apply continuous_pi
  intro e
  exact (continuous_apply e).const_mul _

lemma standardSample_preserving (β : ℝ) (n : ℕ) :
    MeasurePreserving (standardSample β n) (Measure.pi (fun _ : Edge n => gaussianReal 0 1))
      (disorderLaw β n) := by
  refine ⟨(standardSample_continuous β n).measurable,?_⟩
  change Measure.map (fun (z : Edge n → ℝ) (e : Edge n) => sqrt (β^2/n)*z e) _ = _
  rw [Measure.pi_map_pi (fun _ => by fun_prop)]
  unfold disorderLaw
  congr 1
  funext e
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    simp only [NNReal.coe_mk,mul_one,
      sq_sqrt (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)),
      Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))]

lemma hamiltonian_difference_le (g h : Disorder n) (x : Spin n) :
    |hamiltonian g 0 x-hamiltonian h 0 x| ≤ ∑ e,|g e-h e| := by
  rw [hamiltonian_edges,hamiltonian_edges,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ e,|spinValue (x e.1.1)*g e*spinValue (x e.1.2)-
        spinValue (x e.1.1)*h e*spinValue (x e.1.2)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [←sub_mul,←mul_sub,abs_mul,abs_mul]
      cases x e.1.1 <;> cases x e.1.2 <;> simp [spinValue]

lemma log_partition_difference_le (g h : Disorder n) :
    |log (partition g 0)-log (partition h 0)| ≤ ∑ e,|g e-h e| := by
  have hh (g h : Disorder n) : log (partition g 0) ≤ (∑ e,|g e-h e|)+log (partition h 0) := by
    have hp : partition g 0 ≤ exp (∑ e,|g e-h e|)*partition h 0 := by
      unfold partition weight
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      rw [←exp_add]
      apply exp_le_exp.mpr
      have ht := (le_abs_self _).trans (hamiltonian_difference_le g h x)
      linarith
    have ht := log_le_log (partition_pos _ _) hp
    rw [log_mul (exp_ne_zero _) (partition_pos _ _).ne',log_exp] at ht
    exact ht
  have hgh := hh g h
  have hhg := hh h g
  simp_rw [abs_sub_comm (h _) (g _)] at hhg
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma edge_card_bound (n : ℕ) : (Fintype.card (Edge n):ℝ) ≤ (n:ℝ)^2 := by
  have h := Fintype.card_subtype_le (fun p : Fin n × Fin n => p.1 < p.2)
  simp only [Fintype.card_prod,Fintype.card_fin] at h
  exact_mod_cast (show Fintype.card (Edge n) ≤ n^2 from by simpa only [pow_two] using h)

lemma standard_lipschitz_bound (β : ℝ) (n : ℕ) :
    sqrt (β^2/n)*sqrt (Fintype.card (Edge n)) ≤ (|β|+1)*sqrt ((n:ℝ)+1) := by
  by_cases hn : n=0
  · subst n
    simpa using (by positivity : (0:ℝ) ≤ |β|+1)
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have ha : 0 ≤ sqrt (β^2/n)*sqrt (Fintype.card (Edge n)) := by positivity
  have hb : 0 ≤ (|β|+1)*sqrt ((n:ℝ)+1) := by positivity
  apply (sq_le_sq₀ ha hb).mp
  rw [mul_pow,mul_pow,sq_sqrt (div_nonneg (sq_nonneg _) hnR.le),sq_sqrt (Nat.cast_nonneg _),
    sq_sqrt (by positivity : (0:ℝ) ≤ (n:ℝ)+1)]
  have h := mul_le_mul_of_nonneg_left (edge_card_bound n)
    (div_nonneg (sq_nonneg β) hnR.le)
  have he : β^2/(n:ℝ)*(n:ℝ)^2 = β^2*n := by field_simp
  rw [he] at h
  nlinarith [sq_abs β,abs_nonneg β,show (0:ℝ) ≤ n from hnR.le,
    mul_nonneg (abs_nonneg β) hnR.le]

lemma log_partition_standard_lipschitz (β : ℝ) (n : ℕ) :
    LipschitzWith ⟨(|β|+1)*sqrt ((n:ℝ)+1),by positivity⟩
      (fun z : EuclideanSpace ℝ (Edge n) => log (partition (standardSample β n z.ofLp) 0)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z y
  rw [Real.dist_eq]
  calc
    _ ≤ ∑ e, |standardSample β n z.ofLp e-standardSample β n y.ofLp e| :=
      log_partition_difference_le _ _
    _ = sqrt (β^2/n) * ∑ e, |z e-y e| := by
      simp only [standardSample,←mul_sub,abs_mul,abs_of_nonneg (sqrt_nonneg _),Finset.mul_sum]
    _ ≤ sqrt (β^2/n) * (sqrt (Fintype.card (Edge n))*dist z y) := by
      apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
      have hs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Edge n => (1:ℝ))
        (fun e => |z e-y e|)
      simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
        sq_abs,EuclideanSpace.dist_eq,Real.dist_eq] using hs
    _ ≤ ((|β|+1)*sqrt ((n:ℝ)+1))*dist z y := by
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right (standard_lipschitz_bound β n) dist_nonneg

lemma log_partition_integrable (β : ℝ) (n : ℕ) :
    Integrable (fun g : Disorder n => log (partition g 0)) (disorderLaw β n) := by
  have hi := SKRatioGaussian.gaussianProduct_integrable_lipschitz (log_partition_standard_lipschitz β n)
  have hp := standardSample_preserving β n
  exact (hp.integrable_comp (by
    exact ((continuous_partition 0).log (fun g => (partition_pos g 0).ne')).aestronglyMeasurable)).mp hi

lemma log_partition_centered_L1 (β : ℝ) (n : ℕ) :
    (∫ g : Disorder n, |log (partition g 0)-
      ∫ h : Disorder n, log (partition h 0) ∂disorderLaw β n| ∂disorderLaw β n) ≤
      (2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1) := by
  have hp := standardSample_preserving β n
  have hh := SKRatioGaussian.gaussianProduct_centered_L1 (log_partition_standard_lipschitz β n)
    (show (0:ℝ≥0) < ⟨(|β|+1)*sqrt ((n:ℝ)+1),by positivity⟩ from by
      change (0:ℝ)<(|β|+1)*sqrt ((n:ℝ)+1); positivity)
  have hl : Continuous (fun g : Disorder n => log (partition g 0)) :=
    (continuous_partition 0).log (fun g => (partition_pos g 0).ne')
  have he := (integral_map (μ := Measure.pi (fun _ : Edge n => gaussianReal 0 1)) hp.measurable.aemeasurable hl.aestronglyMeasurable).symm
  rw [hp.map_eq] at he
  change (∫ g : Disorder n, log (partition (standardSample β n g) 0)
    ∂Measure.pi (fun _ => gaussianReal 0 1)) = _ at he
  change (∫ g : Disorder n, |log (partition (standardSample β n g) 0)-
    ∫ h : Disorder n, log (partition (standardSample β n h) 0) ∂Measure.pi (fun _ => gaussianReal 0 1)|
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤ _ at hh
  rw [he] at hh
  have he' := (integral_map (μ := Measure.pi (fun _ : Edge n => gaussianReal 0 1)) hp.measurable.aemeasurable
    ((hl.sub (continuous_const (y := ∫ h : Disorder n,log (partition h 0) ∂disorderLaw β n))).abs.aestronglyMeasurable)).symm
  rw [hp.map_eq] at he'
  simp only [Pi.sub_apply] at he'
  rw [he'] at hh
  change _ ≤ (2*exp (π^2/8))*((|β|+1)*sqrt ((n:ℝ)+1)) at hh
  simpa only [mul_assoc] using hh

lemma log_partition_mean_upper (β : ℝ) (n : ℕ) :
    (∫ g : Disorder n, log (partition g 0) ∂disorderLaw β n) ≤
      log ((2:ℝ)^n*exp (normalizingExponent β n)) := by
  let M := (2:ℝ)^n*exp (normalizingExponent β n)
  have hM : 0 < M := by dsimp [M]; positivity
  have hi := integral_mono (log_partition_integrable β n)
    (((integrable_const (log M)).add ((partition_integrable β n).div_const M)).sub (integrable_const 1))
    (fun g => show log (partition g 0) ≤ log M+partition g 0/M-1 from by
      have hh := log_le_sub_one_of_pos (div_pos (partition_pos g 0) hM)
      rw [log_div (partition_pos _ _).ne' hM.ne'] at hh
      linarith)
  simp only [Pi.sub_apply,Pi.add_apply] at hi
  rw [integral_sub (f := fun g => log M+partition g 0/M)
      ((integrable_const _).add ((partition_integrable β n).div_const _)) (integrable_const _),
    integral_add (integrable_const _) ((partition_integrable β n).div_const _),
    integral_const,integral_const,probReal_univ,one_smul,integral_div,integral_partition] at hi
  change _ ≤ log M at ⊢
  simp only [smul_eq_mul,one_mul] at hi
  change _ ≤ log M+M/M-1 at hi
  simpa only [div_self hM.ne',add_sub_cancel_right] using hi

lemma log_partition_mean_lower {β : ℝ} (hβ : β^2 ≤ 1/2) (n : ℕ) :
    log ((2:ℝ)^n*exp (normalizingExponent β n))-log 2-
      8*((2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1)) ≤
      ∫ g : Disorder n, log (partition g 0) ∂disorderLaw β n := by
  let M := (2:ℝ)^n*exp (normalizingExponent β n)
  let m := ∫ g : Disorder n,log (partition g 0) ∂disorderLaw β n
  let L := (2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1)
  have hM : 0 < M := by dsimp [M]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have he : {g : Disorder n | M/2 ≤ partition g 0} =
      {g : Disorder n | log M-log 2 ≤ log (partition g 0)} := by
    ext g
    rw [←log_div hM.ne' (by norm_num)]
    exact (log_le_log_iff (by positivity) (partition_pos g 0)).symm
  have hprob := partition_lower_positive_probability hβ n
  change (1/8:ℝ) ≤ (disorderLaw β n).real {g | M/2 ≤ partition g 0} at hprob
  rw [he] at hprob
  change log M-log 2-8*L ≤ m
  by_cases ha : log M-log 2 ≤ m
  · linarith
  have hc : 0 < log M-log 2-m := by linarith
  have hi : Integrable (fun g : Disorder n => |log (partition g 0)-m|) (disorderLaw β n) :=
    ((log_partition_integrable β n).sub (integrable_const m)).abs
  have hs := mul_meas_ge_le_integral_of_nonneg
    (μ := disorderLaw β n) (f := fun g => |log (partition g 0)-m|)
    (Eventually.of_forall (fun g => abs_nonneg _)) hi (log M-log 2-m)
  have hsub : {g : Disorder n | log M-log 2 ≤ log (partition g 0)} ⊆
      {g : Disorder n | log M-log 2-m ≤ |log (partition g 0)-m|} := by
    intro g hg
    exact (sub_le_sub_right hg m).trans (le_abs_self _)
  have hp := hprob.trans (measureReal_mono (μ := disorderLaw β n) hsub)
  have hmul := mul_le_mul_of_nonneg_left hp hc.le
  have hb := log_partition_centered_L1 β n
  change (∫ g,|log (partition g 0)-m| ∂disorderLaw β n) ≤ L at hb
  linarith

lemma log_partition_annealed_L1 {β : ℝ} (hβ : β^2 ≤ 1/2) (n : ℕ) :
    (∫ g : Disorder n, |log (partition g 0)-
      log ((2:ℝ)^n*exp (normalizingExponent β n))| ∂disorderLaw β n) ≤
      9*((2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1))+log 2 := by
  let a := log ((2:ℝ)^n*exp (normalizingExponent β n))
  let m := ∫ g : Disorder n,log (partition g 0) ∂disorderLaw β n
  let L := (2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1)
  have hu : m ≤ a := log_partition_mean_upper β n
  have hl : a-log 2-8*L ≤ m := log_partition_mean_lower hβ n
  have hi : Integrable (fun g : Disorder n => |log (partition g 0)-m|) (disorderLaw β n) :=
    ((log_partition_integrable β n).sub (integrable_const m)).abs
  have hineq := integral_mono
    (((log_partition_integrable β n).sub (integrable_const a)).abs)
    (hi.add (integrable_const (a-m))) (fun g => show
      |log (partition g 0)-a| ≤ |log (partition g 0)-m|+(a-m) from by
      have hh := abs_sub_le (log (partition g 0)) m a
      rw [abs_of_nonpos (sub_nonpos.mpr hu)] at hh
      linarith)
  simp only [Pi.add_apply,Pi.sub_apply] at hineq
  rw [integral_add hi (integrable_const _),integral_const,probReal_univ,one_smul] at hineq
  have hb : (∫ g,|log (partition g 0)-m| ∂disorderLaw β n) ≤ L := log_partition_centered_L1 β n
  change (∫ g : Disorder n, |log (partition g 0)-a| ∂disorderLaw β n) ≤ 9*L+log 2
  linarith

lemma partition_lower_probability {β κ : ℝ} (hβ : β^2 ≤ 1/2) (hκ : 0 < κ)
    {n : ℕ} (hn : 0 < n) :
    disorderLaw β n {g : Disorder n | partition g 0 <
      ((2:ℝ)^n*exp (normalizingExponent β n))*exp (-κ*n)} ≤
      ENNReal.ofReal ((9*((2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1))+log 2)/(κ*n)) := by
  let M := (2:ℝ)^n*exp (normalizingExponent β n)
  have hM : 0 < M := by dsimp [M]; positivity
  let U := 9*((2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1))+log 2
  let f : Disorder n → ℝ := fun g => |log (partition g 0)-log M|
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hkn : 0 < κ*n := mul_pos hκ hnR
  have hi : Integrable f (disorderLaw β n) :=
    ((log_partition_integrable β n).sub (integrable_const (log M))).abs
  have hs := mul_meas_ge_le_integral_of_nonneg (μ := disorderLaw β n)
    (f := f) (Eventually.of_forall (fun g => abs_nonneg _)) hi (κ*n)
  have hsub : {g : Disorder n | partition g 0 < M*exp (-κ*n)} ⊆
      {g : Disorder n | κ*n ≤ f g} := by
    intro g hg
    have hh := log_lt_log (partition_pos g 0) hg
    rw [log_mul hM.ne' (exp_ne_zero _),log_exp] at hh
    dsimp [f]
    have ht := neg_le_abs (log (partition g 0)-log M)
    linarith
  have hh := mul_le_mul_of_nonneg_left (measureReal_mono (μ := disorderLaw β n) hsub) hkn.le
  have hb := log_partition_annealed_L1 hβ n
  change (∫ g,f g ∂disorderLaw β n) ≤ U at hb
  have hreal : (disorderLaw β n).real {g : Disorder n | partition g 0 < M*exp (-κ*n)} ≤
      U/(κ*n) := by
    apply (le_div_iff₀ hkn).mpr
    rw [mul_comm]
    exact hh.trans (hs.trans hb)
  rw [←ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

lemma sqrt_nat_add_div_tendsto :
    Tendsto (fun n : ℕ => sqrt ((n:ℝ)+1)/(n:ℝ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs := (hi.add (hi.pow 2)).sqrt
  have he : ∀ᶠ n : ℕ in atTop,
      sqrt ((n:ℝ)+1)/(n:ℝ) = sqrt ((n:ℝ)⁻¹+((n:ℝ)⁻¹)^2) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
    rw [show (n:ℝ)⁻¹+((n:ℝ)⁻¹)^2 = ((n:ℝ)+1)/(n:ℝ)^2 by field_simp,
      sqrt_div (by positivity),sqrt_sq hnR.le]
  simpa only [zero_pow (by norm_num : (2:ℕ)≠0),zero_add,sqrt_zero] using
    hs.congr' (he.mono (fun _ h => h.symm))

lemma partition_lower_high_probability {β κ : ℝ} (hβ : β^2 ≤ 1/2) (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => disorderLaw β n {g : Disorder n | partition g 0 <
      ((2:ℝ)^n*exp (normalizingExponent β n))*exp (-κ*n)}) atTop (𝓝 0) := by
  let C := 9*((2*exp (π^2/8))*(|β|+1))
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hreal : Tendsto (fun n : ℕ =>
      (9*((2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1))+log 2)/(κ*n)) atTop (𝓝 0) := by
    have ht := (sqrt_nat_add_div_tendsto.const_mul (C/κ)).add (hi.const_mul (log 2/κ))
    have he (n : ℕ) : (C/κ)*(sqrt ((n:ℝ)+1)/(n:ℝ))+(log 2/κ)*(n:ℝ)⁻¹ =
        (9*((2*exp (π^2/8))*(|β|+1)*sqrt ((n:ℝ)+1))+log 2)/(κ*n) := by
      dsimp [C]
      ring
    simpa only [he,mul_zero,add_zero] using ht
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  simp only [Function.comp_def,ENNReal.ofReal_zero] at he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact partition_lower_probability hβ hκ (by omega)

end SKRatio.Planted

end
end

end OAI
