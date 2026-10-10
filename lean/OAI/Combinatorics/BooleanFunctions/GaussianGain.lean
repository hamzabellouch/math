import OAI.Combinatorics.BooleanFunctions.SmoothGaussian
import OAI.Combinatorics.BooleanFunctions.SmoothSelector

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace GaussianGain
open SmoothGaussian SmoothSelector

theorem gaussian_sq_integral (v : ℝ≥0) :
    (∫ x, x^2 ∂gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (show AEMeasurable (fun x : ℝ => x) (gaussianReal 0 v) from measurable_id.aemeasurable)] at h
  simpa using h

theorem gaussian_sq_integrable (v : ℝ≥0) : Integrable (fun x : ℝ => x^2) (gaussianReal 0 v) := by
  simpa using (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq

theorem gaussian_poly_integrable (v : ℝ≥0) :
    Integrable (fun x : ℝ => 1+x^2) (gaussianReal 0 v) :=
  (integrable_const 1).add (gaussian_sq_integrable v)

theorem density_div_mass_bound {a h δ R t : ℝ} (hh : 0 < h)
    (hδh : δ+h ≤ 1) (ha : |a-(1+t)| ≤ δ) (ht : |t| ≤ R+1) :
    gaussianPDFReal 0 1 t / mass (gaussianReal 0 1) (tent a h) ≤
      2/h * Real.exp (2*R+4) := by
  have hb := tent_mass_pos (a := a) hh
  have hA : |a|+h ≤ |t|+2 := by
    have he : |a| ≤ |a-(1+t)|+|1+t| := by
      simpa using abs_add_le (a-(1+t)) (1+t)
    have he' : |1+t| ≤ 1+|t| := by simpa using abs_add_le (1:ℝ) t
    linarith
  have hsq : (|a|+h)^2 ≤ (|t|+2)^2 := by
    nlinarith [abs_nonneg a, abs_nonneg t]
  have he : Real.exp (-t^2/2) ≤ Real.exp (-((|a|+h)^2)/2) * Real.exp (2*R+4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_abs t]
  apply (div_le_iff₀ hb).mpr
  have hl := beta_lower (a := a) hh
  have hp : 0 ≤ 2/h * Real.exp (2*R+4) := by positivity
  calc
    gaussianPDFReal 0 1 t ≤ (Real.sqrt (2*Real.pi))⁻¹ *
        (Real.exp (-((|a|+h)^2)/2) * Real.exp (2*R+4)) := by
      simpa only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero] using
        mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = (2/h * Real.exp (2*R+4)) *
      (h/2 * ((Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-((|a|+h)^2)/2))) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hl hp

theorem density_tail_bound {R t : ℝ} (ht : R^2 ≤ t^2) :
    gaussianPDFReal 0 1 t ≤ 2 * Real.exp (-(R^2/4)) * gaussianPDFReal 0 2 t := by
  have he : Real.exp (-t^2/2) ≤ Real.exp (-(R^2/4)) * Real.exp (-t^2/4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hs : Real.sqrt (2*Real.pi*2) = Real.sqrt 2 * Real.sqrt (2*Real.pi) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1; ring_nf
  have hs2 : Real.sqrt 2 ≤ (2:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg 2]
  have hs0 : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hc : (Real.sqrt (2*Real.pi))⁻¹ ≤ 2 * (Real.sqrt (2*Real.pi*2))⁻¹ := by
    rw [hs, mul_inv_rev]
    have h : (1:ℝ) ≤ 2 * (Real.sqrt 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))]
      simpa only [one_mul] using hs2
    nlinarith [mul_nonneg (inv_nonneg.mpr hs0.le) (sub_nonneg.mpr h)]
  simp only [gaussianPDFReal, NNReal.coe_one, NNReal.coe_ofNat, mul_one, sub_zero]
  calc
    _ ≤ (2*(Real.sqrt (2*Real.pi*2))⁻¹) *
        (Real.exp (-(R^2/4)) * Real.exp (-t^2/4)) :=
      mul_le_mul hc he (by positivity) (by positivity)
    _ = _ := by ring_nf

def centralKernel (N : ℕ) (δ : ℝ) (μ v β : Fin (2*N+1) → ℝ) (t : ℝ) : ℝ :=
  ∑ i, hat N δ i t * ((1+t-μ i)^2+v i) / β i

@[fun_prop] theorem centralKernel_continuous (N : ℕ) (δ : ℝ)
    (μ v β : Fin (2*N+1) → ℝ) : Continuous (centralKernel N δ μ v β) := by
  unfold centralKernel
  fun_prop

theorem centralKernel_support {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (μ v β : Fin (2*N+1) → ℝ) {t : ℝ} (ht : (N+1)*δ < |t|) :
    centralKernel N δ μ v β t = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : hat N δ i t = 0 := by
    by_contra hn
    exact (not_le_of_gt ht) (hat_support hδ hn)
  simp [hi]

theorem centralKernel_compactSupport {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (μ v β : Fin (2*N+1) → ℝ) : HasCompactSupport (centralKernel N δ μ v β) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(N+1)*δ) (b := (N+1)*δ))
  intro t ht
  apply centralKernel_support hδ
  by_contra hn
  have hh := abs_le.mp (le_of_not_gt hn)
  apply ht
  constructor <;> linarith [hh.1,hh.2]

theorem central_density_bound {N : ℕ} {δ h R M : ℝ} (hδ : 0 < δ)
    (hh : 0 < h) (hsmall : δ+h ≤ 1) (hR : N*δ = R)
    (μ v : Fin (2*N+1) → ℝ)
    (hμ : ∀ i, |μ i-center N δ i| ≤ h) (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ M)
    (t : ℝ) :
    gaussianPDFReal 0 1 t *
      centralKernel N δ μ v (fun i => mass (gaussianReal 0 1) (tent (center N δ i) h)) t ≤
        (2/h * Real.exp (2*R+4)) * ((δ+h)^2+M) := by
  let K := 2/h * Real.exp (2*R+4)
  let B := (δ+h)^2+M
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hM : 0 ≤ M := (hv0 ⟨0,by omega⟩).trans (hv _)
  have hB : 0 ≤ B := add_nonneg (sq_nonneg _) hM
  unfold centralKernel
  rw [Finset.mul_sum]
  calc
    ∑ i, gaussianPDFReal 0 1 t *
        (hat N δ i t * ((1+t-μ i)^2+v i) /
          mass (gaussianReal 0 1) (tent (center N δ i) h)) ≤
        ∑ i, hat N δ i t * (K*B) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : hat N δ i t = 0
      · simp [hi]
      have ha := hat_local hδ hi
      have ht := hat_support hδ hi
      have ht' : |t| ≤ R+1 := by rw [add_mul, hR] at ht; nlinarith
      have he := density_div_mass_bound hh hsmall ha.le ht'
      have herr : |1+t-μ i| ≤ δ+h := by
        have hx : |1+t-μ i| ≤ |center N δ i-(1+t)|+|μ i-center N δ i| := by
          have := abs_add_le (center N δ i-(1+t)) (μ i-center N δ i)
          simpa only [show center N δ i-(1+t)+(μ i-center N δ i) = -(1+t-μ i) by ring_nf,
            abs_neg] using this
        linarith [hμ i]
      have hnum : (1+t-μ i)^2+v i ≤ B := by
        dsimp [B]
        nlinarith [sq_abs (1+t-μ i), abs_nonneg (1+t-μ i), hv i]
      have hnum0 : 0 ≤ (1+t-μ i)^2+v i := add_nonneg (sq_nonneg _) (hv0 i)
      calc
        _ = hat N δ i t *
          ((gaussianPDFReal 0 1 t / mass (gaussianReal 0 1) (tent (center N δ i) h)) *
            ((1+t-μ i)^2+v i)) := by ring_nf
        _ ≤ hat N δ i t * (K*B) :=
          mul_le_mul_of_nonneg_left (mul_le_mul he hnum hnum0 hK) (hat_nonneg ..)
    _ = (∑ i, hat N δ i t) * (K*B) := (Finset.sum_mul ..).symm
    _ ≤ K*B := by nlinarith [hats_sum_le_one N δ t, mul_nonneg hK hB]

theorem central_integral_bound {N : ℕ} {δ h R M : ℝ} (hδ : 0 < δ)
    (hh : 0 < h) (hsmall : δ+h ≤ 1) (hR : N*δ = R)
    (μ v : Fin (2*N+1) → ℝ)
    (hμ : ∀ i, |μ i-center N δ i| ≤ h) (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ M) :
    (∫ t, centralKernel N δ μ v
       (fun i => mass (gaussianReal 0 1) (tent (center N δ i) h)) t ∂gaussianReal 0 1) ≤
      4*(R+δ)/h * Real.exp (2*R+4) * ((δ+h)^2+M) := by
  let β := fun i => mass (gaussianReal 0 1) (tent (center N δ i) h)
  let f := fun t => gaussianPDFReal 0 1 t * centralKernel N δ μ v β t
  have hf : Integrable f volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · dsimp [f]; unfold gaussianPDFReal; fun_prop
    · exact (centralKernel_compactSupport hδ μ v β).mul_left
  have he : ∫ t in Set.Icc (-(R+δ)) (R+δ), f t = ∫ t, f t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    dsimp [f]
    rw [centralKernel_support hδ μ v β]
    · exact mul_zero _
    · by_contra hn
      have hab := abs_le.mp (le_of_not_gt hn)
      rw [add_mul, hR, one_mul] at hab
      exact ht ⟨by linarith [hab.1],hab.2⟩
  have hbound := integral_mono_ae hf.integrableOn (integrable_const
    ((2/h * Real.exp (2*R+4))*((δ+h)^2+M)))
    (ae_of_all (volume.restrict (Set.Icc (-(R+δ)) (R+δ)))
      (central_density_bound hδ hh hsmall hR μ v hμ hv0 hv))
  rw [he] at hbound
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0) ≠ 0)]
  change (∫ t, f t) ≤ _
  apply hbound.trans
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc, smul_eq_mul]
  have hn : 0 ≤ R+δ-(-(R+δ)) := by
    have : 0 ≤ (N:ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
    rw [hR] at this
    linarith
  rw [ENNReal.toReal_ofReal hn]
  ring_nf

  exact le_rfl

theorem density_integrable {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 v)) :
    Integrable (fun t => gaussianPDFReal 0 v t * f t) volume := by
  rw [gaussianReal_of_var_ne_zero 0 hv] at hf
  have he := (integrable_withDensity_iff_integrable_smul₀'
    (show AEMeasurable (gaussianPDF 0 v) volume from
      (show Measurable (gaussianPDF 0 v) from by fun_prop).aemeasurable)
    (ae_of_all _ (fun _ => gaussianPDF_lt_top))).mp hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using he

theorem middle_mass_bound {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (mass (gaussianReal 0 1) (tent 1 h))⁻¹ ≤ 54/h := by
  have hb := tent_mass_pos (a := 1) hh
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs3 : Real.sqrt (2*Real.pi) ≤ 3 := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi),Real.pi_lt_four]
  have hA : (|(1:ℝ)|+h)^2/2 ≤ 2 := by norm_num only [abs_one]; nlinarith
  have he : Real.exp (-2) ≤ Real.exp (-((|(1:ℝ)|+h)^2)/2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hl : h/6*Real.exp (-2) ≤ mass (gaussianReal 0 1) (tent 1 h) := by
    apply le_trans _ (beta_lower hh)
    have hi : (1:ℝ)/3 ≤ (Real.sqrt (2*Real.pi))⁻¹ := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le hs hs3
    have hm := mul_le_mul hi he (Real.exp_pos (-2)).le (inv_nonneg.mpr hs.le)
    have hp := mul_le_mul_of_nonneg_left hm (show 0 ≤ h/2 by positivity)
    nlinarith
  have hE : Real.exp 2 ≤ 9 := by
    calc Real.exp 2 = (Real.exp 1)^2 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 3^2 := pow_le_pow_left₀ (Real.exp_pos _).le (le_trans Real.exp_one_lt_d9.le (by norm_num)) _
      _ = 9 := by norm_num
  have hlim : (mass (gaussianReal 0 1) (tent 1 h))⁻¹ ≤ 6/h * Real.exp 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hb]
    have heq : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
    have hp := mul_le_mul_of_nonneg_right hl (show 0 ≤ 6/h*Real.exp 2 by positivity)
    calc 1 = (h/6*Real.exp (-2)) * (6/h*Real.exp 2) := by
           field_simp; nlinarith [heq]
      _ ≤ _ := by simpa only [mul_comm] using hp
  apply hlim.trans
  calc 6/h * Real.exp 2 ≤ 6/h*9 :=
      mul_le_mul_of_nonneg_left hE (show 0 ≤ 6/h by positivity)
    _ = 54/h := by ring_nf

def residual (N : ℕ) (δ t : ℝ) : ℝ := 1-∑ i, hat N δ i t

theorem residual_nonneg (N : ℕ) (δ t : ℝ) : 0 ≤ residual N δ t :=
  sub_nonneg.mpr (hats_sum_le_one ..)

theorem residual_le_one (N : ℕ) (δ t : ℝ) : residual N δ t ≤ 1 := by
  have : 0 ≤ ∑ i, hat N δ i t := Finset.sum_nonneg (fun _ _ => hat_nonneg ..)
  dsimp [residual]; linarith

theorem residual_eq_zero {N : ℕ} {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ N*δ) :
    residual N δ t = 0 := by simp only [residual, hats_sum_eq_one hδ ht, sub_self]

theorem quadratic_integrable (c v : ℝ) (σ : ℝ≥0) :
    Integrable (fun t : ℝ => (1+t-c)^2+v) (gaussianReal 0 σ) := by
  have h0 : Integrable (fun _ : ℝ => (1-c)^2+v) (gaussianReal 0 σ) := integrable_const _
  have h1 : Integrable (fun t : ℝ => t) (gaussianReal 0 σ) :=
    (memLp_id_gaussianReal (μ := 0) (v := σ) 1).integrable (by norm_num)
  have h2 := gaussian_sq_integrable σ
  convert! (h2.add (h1.const_mul (2*(1-c)))).add h0 using 1
  funext t; simp only [Pi.add_apply]; ring_nf

theorem residual_quadratic_integrable {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (c v : ℝ) :
    Integrable (fun t => residual N δ t *((1+t-c)^2+v)) (gaussianReal 0 1) := by
  have hi (i : Fin (2*N+1)) : Integrable (fun t => hat N δ i t *((1+t-c)^2+v)) (gaussianReal 0 1) :=
    (by fun_prop : Continuous (fun t => hat N δ i t *((1+t-c)^2+v))).integrable_of_hasCompactSupport
      ((hat_compactSupport hδ i).mul_right)
  convert! (quadratic_integrable c v 1).sub (integrable_finsetSum _ (fun i _ => hi i)) using 1
  funext t
  simp only [Pi.sub_apply]
  dsimp [residual]
  rw [sub_mul,one_mul,Finset.sum_mul]

theorem tail_integral_bound {N : ℕ} {δ h R c v : ℝ} (hδ : 0 < δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hR : N*δ = R) (hc : |c-1| ≤ h)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∫ t, residual N δ t * ((1+t-c)^2+v) / mass (gaussianReal 0 1) (tent 1 h) ∂gaussianReal 0 1) ≤
      972/h * Real.exp (-(R^2/4)) := by
  let β := mass (gaussianReal 0 1) (tent 1 h)
  have hb : 0 < β := tent_mass_pos hh
  have hβ : β⁻¹ ≤ 54/h := middle_mass_bound hh hh1
  have hi : Integrable (fun t => gaussianPDFReal 0 1 t *
      (residual N δ t*((1+t-c)^2+v)/β)) volume :=
    density_integrable (by norm_num) ((residual_quadratic_integrable hδ c v).div_const β)
  have hj : Integrable (fun t => (324/h*Real.exp (-(R^2/4))) *
      (gaussianPDFReal 0 2 t*(1+t^2))) volume :=
    (density_integrable (by norm_num) (gaussian_poly_integrable 2)).const_mul _
  have hpoint (t : ℝ) : gaussianPDFReal 0 1 t *
      (residual N δ t*((1+t-c)^2+v)/β) ≤ (324/h*Real.exp (-(R^2/4))) *
      (gaussianPDFReal 0 2 t*(1+t^2)) := by
    by_cases ht : |t| ≤ R
    · rw [residual_eq_zero hδ (by rwa [hR])]
      simp only [zero_mul,zero_div,mul_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (gaussianPDFReal_nonneg ..) (by positivity))
    have hR0 : 0 ≤ R := by rw [← hR]; positivity
    have htsq : R^2 ≤ t^2 := by nlinarith [sq_abs t, abs_nonneg t,lt_of_not_ge ht]
    have hd := density_tail_bound htsq
    have hn : (1+t-c)^2+v ≤ 3*(1+t^2) := by
      have hc' := abs_le.mp hc
      nlinarith [sq_nonneg (t-(1-c)),sq_nonneg t]
    have hn0 : 0 ≤ (1+t-c)^2+v := add_nonneg (sq_nonneg _) hv0
    have hrn : residual N δ t*((1+t-c)^2+v) ≤ 3*(1+t^2) := by
      have := mul_le_mul (residual_le_one N δ t) hn hn0 (by norm_num : (0:ℝ)≤1)
      simpa using this
    have hq : residual N δ t*((1+t-c)^2+v)/β ≤ (54/h)*(3*(1+t^2)) := by
      rw [div_eq_mul_inv]
      calc _ ≤ (3*(1+t^2))*(54/h) := mul_le_mul hrn hβ (inv_nonneg.mpr hb.le) (by positivity)
        _ = _ := by ring_nf
    calc
      _ ≤ (2*Real.exp (-(R^2/4))*gaussianPDFReal 0 2 t) * ((54/h)*(3*(1+t^2))) :=
        mul_le_mul hd hq (div_nonneg (mul_nonneg (residual_nonneg N δ t) hn0) hb.le)
          (mul_nonneg (by positivity) (gaussianPDFReal_nonneg ..))
      _ = _ := by ring_nf
  have hbound := integral_mono hi hj hpoint
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0)≠0)]
  change (∫ t, gaussianPDFReal 0 1 t*(residual N δ t*((1+t-c)^2+v)/β)) ≤ _
  apply hbound.trans
  rw [integral_const_mul]
  change _ * (∫ t, gaussianPDFReal 0 2 t • (1+t^2)) ≤ _
  rw [← integral_gaussianReal_eq_integral_smul (by norm_num : (2:ℝ≥0)≠0)]
  rw [integral_add (integrable_const 1) (gaussian_sq_integrable 2), integral_const,
    gaussian_sq_integral]
  norm_num
  ring_nf
  exact le_rfl

def gridN : ℕ := (2^128)^8
def width : ℝ := 1 / ((2:ℝ)^128)^12
def radius : ℝ := 96
def step : ℝ := radius / gridN

theorem gridN_pos : 0 < gridN := by norm_num [gridN]
theorem width_pos : 0 < width := by unfold width; positivity
theorem step_pos : 0 < step := by
  exact div_pos (by norm_num [radius]) (by exact_mod_cast gridN_pos)
theorem step_small : step+width ≤ 1 := by norm_num [step,radius,gridN,width]
theorem width_le_one : width ≤ 1 := by linarith [step_small,step_pos]
theorem grid_radius : (gridN:ℝ)*step = radius := by
  unfold step; field_simp [show (gridN:ℝ)≠0 by exact_mod_cast gridN_pos.ne']
theorem variance_numeric : (2*gridN+1:ℝ)*width^2 < 1/4 := by
  norm_num [gridN,width]

theorem central_numeric :
    4*(radius+step)/width * Real.exp (2*radius+4) *
      ((step+width)^2+(2*gridN+1:ℝ)*width^2) < 1/4 := by
  have he : Real.exp 196 < (3:ℝ)^196 := by
    calc Real.exp 196 = (Real.exp 1)^196 := by rw [← Real.exp_nat_mul]; norm_num
      _ < 3^196 := pow_lt_pow_left₀ (lt_trans Real.exp_one_lt_d9 (by norm_num))
        (Real.exp_pos _).le (by norm_num)
  have hp : 0 < 4*(radius+step)/width*((step+width)^2+(2*gridN+1:ℝ)*width^2) := by
    dsimp [radius,step,width,gridN]; positivity
  calc _ = Real.exp 196 * (4*(radius+step)/width*((step+width)^2+(2*gridN+1:ℝ)*width^2)) := by
           norm_num [radius]; ring_nf
    _ < 3^196 * (4*(radius+step)/width*((step+width)^2+(2*gridN+1:ℝ)*width^2)) :=
      mul_lt_mul_of_pos_right he hp
    _ < 1/4 := by norm_num [radius,step,width,gridN]

theorem tail_numeric : 972/width*Real.exp (-(radius^2/4)) < 1/4 := by
  have he : (2:ℝ)^2304 < Real.exp 2304 := by
    calc (2:ℝ)^2304 < (Real.exp 1)^2304 :=
           pow_lt_pow_left₀ (lt_trans (by norm_num) Real.exp_one_gt_d9) (by norm_num) (by norm_num)
      _ = Real.exp 2304 := by rw [← Real.exp_nat_mul]; norm_num
  have hi : Real.exp (-2304) < ((2:ℝ)^2304)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_lt_inv₀ (Real.exp_pos _) (by positivity)).mpr he
  calc _ = 972/width*Real.exp (-2304) := by norm_num [radius]
    _ < 972/width*((2:ℝ)^2304)⁻¹ := mul_lt_mul_of_pos_left hi (by unfold width; positivity)
    _ < 1/4 := by
      rw [show (2:ℝ)^2304 = ((2:ℝ)^128)^18 by rw [← pow_mul]]
      norm_num [width]

abbrev Leaves := Fin (2*gridN+1)
def leafTest (i : Leaves) : ℝ → ℝ := tent (center gridN step i) width
def selectorTest (i : Leaves) : ℝ → ℝ := weight gridN step i
def beta (i : Leaves) : ℝ := mass (gaussianReal 0 1) (leafTest i)
def mu (i : Leaves) : ℝ := mean (gaussianReal 0 1) (leafTest i)
def sigma (i : Leaves) : ℝ := variance (gaussianReal 0 1) (leafTest i)
def totalVariance : ℝ := ∑ i, sigma i
def otherVariance (i : Leaves) : ℝ := ∑ j ∈ Finset.univ.erase i, sigma j

theorem beta_pos (i : Leaves) : 0 < beta i := tent_mass_pos width_pos
theorem mu_close (i : Leaves) : |mu i-center gridN step i| ≤ width :=
  (tent_moments width_pos).1
theorem sigma_nonneg (i : Leaves) : 0 ≤ sigma i := (tent_moments width_pos).2.1
theorem sigma_bound (i : Leaves) : sigma i ≤ width^2 := (tent_moments width_pos).2.2
theorem otherVariance_nonneg (i : Leaves) : 0 ≤ otherVariance i :=
  Finset.sum_nonneg (fun _ _ => sigma_nonneg _)
theorem otherVariance_bound (i : Leaves) : otherVariance i ≤ (2*gridN+1:ℝ)*width^2 := by
  calc otherVariance i ≤ ∑ j : Leaves, sigma j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun j _ _ => sigma_nonneg j)
    _ ≤ ∑ _ : Leaves, width^2 := Finset.sum_le_sum (fun j _ => sigma_bound j)
    _ = _ := by simp [Leaves]
theorem otherVariance_le_one (i : Leaves) : otherVariance i ≤ 1 :=
  (otherVariance_bound i).trans (le_trans variance_numeric.le (by norm_num))

def kernel (t : ℝ) : ℝ := ∑ i, selectorTest i t *((1+t-mu i)^2+otherVariance i)/beta i

def J : ℝ := ∫ t, kernel t ∂gaussianReal 0 1

theorem kernel_split_general (N : ℕ) (δ : ℝ) (μ v β : Fin (2*N+1) → ℝ) (t : ℝ) :
    (∑ i, weight N δ i t *((1+t-μ i)^2+v i)/β i) = centralKernel N δ μ v β t +
    residual N δ t *((1+t-μ (middle N))^2+v (middle N))/β (middle N) := by
  unfold weight centralKernel residual
  simp only [add_mul,add_div,Finset.sum_add_distrib]
  congr 1
  simp only [ite_mul,zero_mul,ite_div,zero_div,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem kernel_split (t : ℝ) : kernel t = centralKernel gridN step mu otherVariance beta t +
    residual gridN step t *((1+t-mu (middle gridN))^2+otherVariance (middle gridN))/beta (middle gridN) :=
  kernel_split_general gridN step mu otherVariance beta t

theorem kernel_integrable : Integrable kernel (gaussianReal 0 1) := by
  rw [show kernel = fun t => centralKernel gridN step mu otherVariance beta t +
    residual gridN step t *((1+t-mu (middle gridN))^2+otherVariance (middle gridN))/beta (middle gridN)
      from funext kernel_split]
  exact ((centralKernel_continuous ..).integrable_of_hasCompactSupport
    (centralKernel_compactSupport step_pos ..)).add
      ((residual_quadratic_integrable step_pos _ _).div_const _)

theorem J_lt_half : J < 1/2 := by
  have hc := central_integral_bound step_pos width_pos step_small grid_radius mu otherVariance
    mu_close otherVariance_nonneg otherVariance_bound
  have ht := tail_integral_bound step_pos width_pos width_le_one grid_radius
    (show |mu (middle gridN)-1| ≤ width by simpa using mu_close (middle gridN))
    (otherVariance_nonneg (middle gridN)) (otherVariance_le_one (middle gridN))
  have hb : beta (middle gridN) = mass (gaussianReal 0 1) (tent 1 width) := by
    simp [beta,leafTest]
  unfold J
  simp_rw [kernel_split]
  rw [integral_add ((centralKernel_continuous ..).integrable_of_hasCompactSupport
    (centralKernel_compactSupport step_pos ..))
      ((residual_quadratic_integrable step_pos _ _).div_const _), hb]
  change (∫ t, centralKernel gridN step mu otherVariance beta t ∂gaussianReal 0 1) + _ < _
  change (∫ t, centralKernel gridN step mu otherVariance beta t ∂gaussianReal 0 1) ≤ _ at hc
  linarith [central_numeric,tail_numeric]

theorem J_nonneg : 0 ≤ J := by
  apply integral_nonneg
  intro t
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (mul_nonneg (weight_nonneg ..)
    (add_nonneg (sq_nonneg _) (otherVariance_nonneg _))) (beta_pos _).le

theorem positive_gaussian_deficit :
    0 < (∏ i : Leaves, beta i) * (1+totalVariance-J) := by
  have hp : 0 < ∏ i : Leaves, beta i := Finset.prod_pos (fun _ _ => beta_pos _)
  have hs : 0 ≤ totalVariance := Finset.sum_nonneg (fun _ _ => sigma_nonneg _)
  exact mul_pos hp (by linarith [J_lt_half])

end GaussianGain
end SquareRootDegree

end

end OAI
