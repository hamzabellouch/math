import Mathlib
import OAI.Probability.SKRatio.Variational.ScalarMoments

namespace OAI

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

lemma multiplier_strict_pos (h : ℝ) : 0 < multiplier h := by
  linarith [multiplier_pos h]

lemma abs_inv_multiplier_le (h : ℝ) : |(multiplier h)⁻¹| ≤ 3 := by
  rw [abs_of_pos (inv_pos.mpr (multiplier_strict_pos h)),inv_eq_one_div,div_le_iff₀ (multiplier_strict_pos h)]
  linarith [multiplier_pos h]

lemma continuous_inv_multiplier : Continuous (fun h => (multiplier h)⁻¹) :=
  continuous_multiplier.inv₀ (fun h => (multiplier_strict_pos h).ne')

lemma abs_v_sum_le (h t : ℝ) : |v h+v t| ≤ 2 := by
  rw [abs_of_nonneg (add_nonneg (v_pos h).le (v_pos t).le)]
  linarith [v_le_one h,v_le_one t]

lemma v_sum_sq_le (h t : ℝ) : (v h+v t)^2 ≤ 4 := by
  nlinarith [abs_v_sum_le h t,neg_le_abs (v h+v t),le_abs_self (v h+v t)]

lemma abs_diagonal_kernel_le (h t : ℝ) : |v t^2/(w h+w t)| ≤ 2 := by
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (add_pos (w_pos h) (w_pos t)).le)]
  apply (div_le_iff₀ (add_pos (w_pos h) (w_pos t))).mpr
  have ht : v t ≤ 2*w t := by rw [v_factor]; nlinarith [w_pos t,(m_bounds t).2]
  have hv : v t^2 ≤ v t := by nlinarith [v_pos t,v_le_one t]
  linarith [w_pos h]

lemma continuous_diagonal_kernel :
    Continuous (fun z : ℝ×ℝ => v z.2^2/(w z.1+w z.2)) := by
  apply ((continuous_v.comp continuous_snd).pow 2).div
    ((continuous_w.comp continuous_fst).add (continuous_w.comp continuous_snd))
  intro z
  exact (add_pos (w_pos z.1) (w_pos z.2)).ne'

section Probability
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

def diagonal (β : ℝ) (h : ℝ) : ℝ :=
  β^2 * ∫ t, v t^2/(w h+w t) ∂μ

def cost (β : ℝ) (t : ℝ) : ℝ :=
  ∫ h, (β^2/4)*(v h+v t)^2/(multiplier h) ∂μ

lemma integrable_multiplier : Integrable multiplier μ := by
  apply (integrable_const (76/100:ℝ)).mono' continuous_multiplier.aestronglyMeasurable
  exact ae_of_all _ (fun h => by
    simpa only [norm_eq_abs,abs_of_pos (multiplier_strict_pos h)] using multiplier_le h)

lemma mean_multiplier_pos : 0 < ∫ h, multiplier h ∂μ := by
  have h := integral_mono (integrable_const (4464/10000:ℝ)) (integrable_multiplier μ)
    multiplier_pos
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at h
  linarith

lemma continuous_diagonal (β : ℝ) : Continuous (diagonal μ β) := by
  apply Continuous.const_mul
  apply continuous_of_dominated (bound := fun _ => (2:ℝ))
  · intro h
    exact (continuous_diagonal_kernel.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro h
    exact ae_of_all _ (fun t => by simpa only [norm_eq_abs] using abs_diagonal_kernel_le h t)
  · exact integrable_const _
  · apply ae_of_all
    intro t
    exact continuous_const.div (continuous_w.add continuous_const)
      (fun h => (add_pos (w_pos h) (w_pos t)).ne')

lemma abs_diagonal_le (β h : ℝ) : |diagonal μ β h| ≤ 2*β^2 := by
  have hb : |∫ t, v t^2/(w h+w t) ∂μ| ≤ 2 := by
    exact (abs_integral_le_integral_abs).trans (by
      simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,Function.comp_apply,id_eq] using
      integral_mono ((integrable_const (μ := μ) (2:ℝ)).mono'
        (continuous_diagonal_kernel.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        (ae_of_all _ (fun t => by simpa only [norm_eq_abs,Function.comp_apply,id_eq] using abs_diagonal_kernel_le h t))).abs
        (integrable_const 2) (abs_diagonal_kernel_le h))
  unfold diagonal
  rw [abs_mul,abs_of_nonneg (sq_nonneg β)]
  nlinarith [sq_nonneg β]

lemma abs_cost_integrand_le (β h t : ℝ) :
    |(β^2/4)*(v h+v t)^2/(multiplier h)| ≤ 3*β^2 := by
  rw [div_eq_mul_inv,abs_mul,abs_mul,abs_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num)),
    abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (β^2/4)*4*3 := by
      gcongr
      · exact v_sum_sq_le h t
      · exact abs_inv_multiplier_le h
    _ = _ := by ring

lemma continuous_cost_integrand (β : ℝ) :
    Continuous (fun z : ℝ×ℝ => (β^2/4)*(v z.1+v z.2)^2/(multiplier z.1)) := by
  exact ((((continuous_v.comp continuous_fst).add (continuous_v.comp continuous_snd)).pow 2).const_mul _).div
    (continuous_multiplier.comp continuous_fst) (fun z => (multiplier_strict_pos z.1).ne')

lemma continuous_cost (β : ℝ) : Continuous (cost μ β) := by
  apply continuous_of_dominated (bound := fun _ => 3*β^2)
  · intro t
    exact ((continuous_cost_integrand β).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · intro t
    exact ae_of_all _ (fun h => by simpa only [norm_eq_abs] using abs_cost_integrand_le β h t)
  · exact integrable_const _
  · apply ae_of_all
    intro h
    exact (((continuous_const.add continuous_v).pow 2).const_mul _).div_const _

lemma abs_cost_le (β t : ℝ) : |cost μ β t| ≤ 3*β^2 := by
  unfold cost
  apply abs_integral_le_integral_abs.trans
  have hI : Integrable (fun h => (β^2/4)*(v h+v t)^2/(multiplier h)) μ := by
    exact (integrable_const (3*β^2)).mono'
      (((continuous_cost_integrand β).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (ae_of_all _ (fun h => by simpa only [norm_eq_abs] using abs_cost_integrand_le β h t))
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,Function.comp_apply,id_eq] using
    integral_mono hI.abs (integrable_const (3*β^2)) (fun h => abs_cost_integrand_le β h t)

variable {μ}

omit [IsProbabilityMeasure μ] in
lemma memLp_v_sum_mul {b : ℝ → ℝ} (hb : MemLp b 2 μ) (h : ℝ) :
    MemLp (fun t => (v h+v t)*b t) 2 μ := by
  apply hb.of_le_mul (((continuous_const.add continuous_v).aestronglyMeasurable).mul
    hb.aestronglyMeasurable) (c := (2:ℝ))
  exact ae_of_all _ (fun t => by
    change |(v h+v t)*b t| ≤ 2*|b t|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_v_sum_le h t) (abs_nonneg _))

lemma integral_v_sum_mul {b : ℝ → ℝ} (hb : MemLp b 2 μ) (h : ℝ) :
    ∫ t, (v h+v t)*b t ∂μ = (∫ t, b t*v t ∂μ)+v h*(∫ t, b t ∂μ) := by
  have hbI := hb.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hbvI : Integrable (fun t => b t*v t) μ := hb.integrable_mul (memLp_v (p := 2))
  have he : (fun t => (v h+v t)*b t) = fun t => b t*v t+v h*b t := by funext t; ring
  rw [he,integral_add hbvI (hbI.const_mul _),integral_const_mul]

def radicand (μ : Measure ℝ) (b r : ℝ → ℝ) (h : ℝ) : ℝ :=
  (∫ t, ((v h+v t)*r t)^2 ∂μ) +
    (∫ t, ((v h+v t)*b t - (∫ s, (v h+v s)*b s ∂μ))^2 ∂μ)

omit [IsProbabilityMeasure μ] in
lemma radicand_nonneg (b r : ℝ → ℝ) (h : ℝ) : 0 ≤ radicand μ b r h :=
  add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))

lemma integral_centered_sq {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    ∫ h, (f h-(∫ t, f t ∂μ))^2 ∂μ =
      (∫ h, f h^2 ∂μ)-(∫ h, f h ∂μ)^2 := by
  have hI := hf.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hid (h : ℝ) : (f h-(∫ t, f t ∂μ))^2 =
      f h^2-(2*(∫ t, f t ∂μ))*f h+(∫ t, f t ∂μ)^2 := by ring
  simp_rw [hid]
  have hsub : Integrable (fun h => f h^2-(2*(∫ t, f t ∂μ))*f h) μ :=
    hf.integrable_sq.sub (hI.const_mul _)
  rw [integral_add hsub (integrable_const _),
    integral_sub hf.integrable_sq (hI.const_mul _),integral_const_mul,integral_const]
  simp only [probReal_univ,smul_eq_mul,one_mul]
  ring

omit [IsProbabilityMeasure μ] in
lemma v_sum_square_integrable {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (h : ℝ) : Integrable (fun t => (v h+v t)^2*(b t^2+r t^2)) μ := by
  have he : (fun t => (v h+v t)^2*(b t^2+r t^2)) =
      fun t => ((v h+v t)*b t)^2+((v h+v t)*r t)^2 := by funext t; ring
  rw [he]
  exact (memLp_v_sum_mul hb h).integrable_sq.add (memLp_v_sum_mul hr h).integrable_sq

lemma radicand_expansion {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (h : ℝ) : radicand μ b r h =
      (∫ t, (v h+v t)^2*(b t^2+r t^2) ∂μ) -
        ((∫ t, b t*v t ∂μ)+v h*(∫ t, b t ∂μ))^2 := by
  rw [radicand,integral_centered_sq (memLp_v_sum_mul hb h),integral_v_sum_mul hb h]
  have he : (fun t => (v h+v t)^2*(b t^2+r t^2)) =
      fun t => ((v h+v t)*b t)^2+((v h+v t)*r t)^2 := by funext t; ring
  rw [he,integral_add (memLp_v_sum_mul hb h).integrable_sq (memLp_v_sum_mul hr h).integrable_sq]
  ring

lemma radicand_le {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ)
    (h : ℝ) : radicand μ b r h ≤ 4*∫ t, b t^2+r t^2 ∂μ := by
  rw [radicand_expansion hb hr h]
  have hI := hb.integrable_sq.add hr.integrable_sq
  have he := integral_mono (v_sum_square_integrable hb hr h) (hI.const_mul (4:ℝ))
    (fun t => mul_le_mul_of_nonneg_right (v_sum_sq_le h t) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  simp only [integral_const_mul,Pi.add_apply] at he
  nlinarith [sq_nonneg ((∫ t, b t*v t ∂μ)+v h*(∫ t, b t ∂μ))]

lemma continuous_radicand {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ) :
    Continuous (radicand μ b r) := by
  have he : radicand μ b r = fun h =>
    (∫ t, (v h+v t)^2*(b t^2+r t^2) ∂μ) -
      ((∫ t, b t*v t ∂μ)+v h*(∫ t, b t ∂μ))^2 := funext (radicand_expansion hb hr)
  rw [he]
  apply Continuous.sub
  · apply continuous_of_dominated (bound := fun t => 4*(b t^2+r t^2))
    · intro h
      exact (v_sum_square_integrable hb hr h).aestronglyMeasurable
    · intro h
      apply ae_of_all
      intro t
      rw [norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))]
      exact mul_le_mul_of_nonneg_right (v_sum_sq_le h t) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    · exact (hb.integrable_sq.add hr.integrable_sq).const_mul _
    · exact ae_of_all _ (fun t => ((continuous_v.add continuous_const).pow 2).mul_const _)
  · exact (continuous_const.add (continuous_v.mul_const _)).pow 2

lemma memLp_sqrt_radicand {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ) :
    MemLp (fun h => sqrt (radicand μ b r h)) 2 μ := by
  apply MemLp.of_bound (continuous_sqrt.comp (continuous_radicand hb hr)).aestronglyMeasurable
    (sqrt (4*∫ t, b t^2+r t^2 ∂μ))
  exact ae_of_all _ (fun h => by
    simpa only [Function.comp_apply,norm_eq_abs,abs_of_nonneg (sqrt_nonneg _)] using
      sqrt_le_sqrt (radicand_le hb hr h))

lemma integrable_radical {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ) :
    Integrable (fun h => r h*sqrt (radicand μ b r h)) μ :=
  hr.integrable_mul (memLp_sqrt_radicand hb hr)

lemma memLp_multiplier : MemLp multiplier 2 μ := by
  apply MemLp.of_bound continuous_multiplier.aestronglyMeasurable (76/100:ℝ)
  exact ae_of_all _ (fun h => by
    simpa only [norm_eq_abs,abs_of_pos (multiplier_strict_pos h)] using multiplier_le h)

lemma integral_weighted_square {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    (∫ h, f h ∂μ)^2 / (∫ h, multiplier h ∂μ) ≤
      ∫ h, f h^2/(multiplier h) ∂μ := by
  have hF : Integrable f μ := hf.integrable (by norm_num)
  have hQ : Integrable (fun h => f h^2/(multiplier h)) μ := by
    simp_rw [div_eq_mul_inv]
    exact hf.integrable_sq.mul_bdd continuous_inv_multiplier.aestronglyMeasurable
      (ae_of_all _ (fun h => by simpa only [norm_eq_abs] using abs_inv_multiplier_le h))
  let l := ∫ h, multiplier h ∂μ
  have hl : 0 < l := mean_multiplier_pos μ
  let c := (∫ h, f h ∂μ)/l
  have hid (h : ℝ) : (f h-c*multiplier h)^2/(multiplier h) =
      f h^2/(multiplier h)-(2*c)*f h+c^2*multiplier h := by
    field_simp [(multiplier_strict_pos h).ne']
    ring
  have hnonneg : 0 ≤ ∫ h, (f h-c*multiplier h)^2/(multiplier h) ∂μ :=
    integral_nonneg (fun h => div_nonneg (sq_nonneg _) (multiplier_strict_pos h).le)
  have hsub : Integrable (fun h => f h^2/(multiplier h)-(2*c)*f h) μ :=
    hQ.sub (hF.const_mul _)
  simp_rw [hid] at hnonneg
  rw [integral_add hsub ((integrable_multiplier μ).const_mul _),
    integral_sub hQ (hF.const_mul _),integral_const_mul,integral_const_mul] at hnonneg
  have hc : c*l = ∫ h, f h ∂μ := div_mul_cancel₀ _ hl.ne'
  change (∫ h, f h ∂μ)^2/l ≤ _
  apply (div_le_iff₀ hl).mpr
  have hn := mul_nonneg hl.le hnonneg
  change 0 ≤ l*((∫ h, f h^2/multiplier h ∂μ)-(2*c)*(∫ h, f h ∂μ)+c^2*l) at hn
  nlinarith only [hn,sq_nonneg (c*l-(∫ h, f h ∂μ)),hc]

lemma young_radical_pointwise (β r T Λ : ℝ) (hT : 0 ≤ T) (hΛ : 0 < Λ) :
    β*r*sqrt T ≤ Λ*r^2+(β^2/4)*T/Λ := by
  have hs := sq_nonneg (β*sqrt T-2*Λ*r)
  have hsqrt := sq_sqrt hT
  apply (mul_le_mul_iff_of_pos_right (show 0 < 4*Λ by positivity)).mp
  have hd : (Λ*r^2+(β^2/4)*T/Λ)*(4*Λ) = 4*Λ^2*r^2+β^2*T := by
    field_simp
  rw [hd]
  nlinarith only [hs,hsqrt]

lemma cost_product_integrable (β : ℝ) {Z : ℝ → ℝ} (hZ : Integrable Z μ) :
    Integrable (fun z : ℝ×ℝ =>
      ((β^2/4)*(v z.1+v z.2)^2/multiplier z.1)*Z z.2) (μ.prod μ) := by
  exact (hZ.comp_snd μ).bdd_mul (continuous_cost_integrand β).aestronglyMeasurable
    (ae_of_all _ (fun z => by
      simpa only [norm_eq_abs] using abs_cost_integrand_le β z.1 z.2))

lemma cost_fubini (β : ℝ) {Z : ℝ → ℝ} (hZ : Integrable Z μ) :
    ∫ h, (β^2/4)*(∫ t, (v h+v t)^2*Z t ∂μ)/multiplier h ∂μ =
      ∫ t, cost μ β t*Z t ∂μ := by
  have hI := cost_product_integrable β hZ
  have he (h : ℝ) : (β^2/4)*(∫ t, (v h+v t)^2*Z t ∂μ)/multiplier h =
      ∫ t, ((β^2/4)*(v h+v t)^2/multiplier h)*Z t ∂μ := by
    rw [div_eq_mul_inv,←integral_const_mul,←integral_mul_const]
    apply integral_congr_ae
    exact ae_of_all _ (fun t => by ring)
  simp_rw [he]
  rw [integral_integral_swap hI]
  simp_rw [integral_mul_const]
  rfl

lemma integrable_cost_quadratic (β : ℝ) {b r : ℝ → ℝ}
    (hb : MemLp b 2 μ) (hr : MemLp r 2 μ) :
    Integrable (fun h => cost μ β h*(b h^2+r h^2)) μ := by
  exact (hb.integrable_sq.add hr.integrable_sq).bdd_mul
    (continuous_cost μ β).aestronglyMeasurable
    (ae_of_all _ (fun h => by simpa only [norm_eq_abs] using abs_cost_le μ β h))

omit [IsProbabilityMeasure μ] in
lemma integrable_multiplier_square {r : ℝ → ℝ} (hr : MemLp r 2 μ) :
    Integrable (fun h => multiplier h*r h^2) μ := by
  exact hr.integrable_sq.bdd_mul continuous_multiplier.aestronglyMeasurable
    (ae_of_all _ (fun h => by
      simpa only [norm_eq_abs,abs_of_pos (multiplier_strict_pos h)] using multiplier_le h))

lemma memLp_linear_v (A B : ℝ) : MemLp (fun h => B+v h*A) 2 μ :=
  (memLp_const B).add (memLp_v.mul_const A)

lemma integral_linear_v (A B : ℝ) :
    ∫ h, B+v h*A ∂μ = B+(∫ h, v h ∂μ)*A := by
  have hv : Integrable v μ := memLp_v.integrable (by norm_num : (1:ENNReal) ≤ 2)
  rw [integral_add (integrable_const _) (hv.mul_const _),integral_const,integral_mul_const]
  simp only [probReal_univ,smul_eq_mul,one_mul]

lemma integrable_linear_v_cost (β A B : ℝ) :
    Integrable (fun h => (β^2/4)*(B+v h*A)^2/multiplier h) μ := by
  simp_rw [div_eq_mul_inv,mul_assoc]
  exact ((memLp_linear_v A B (μ := μ)).integrable_sq.mul_bdd
    continuous_inv_multiplier.aestronglyMeasurable
    (ae_of_all _ (fun h => by simpa only [norm_eq_abs] using abs_inv_multiplier_le h))).const_mul (4:ℝ)⁻¹ |>.const_mul (β^2)

lemma radical_young (β : ℝ) {b r : ℝ → ℝ} (hb : MemLp b 2 μ) (hr : MemLp r 2 μ) :
    β*(∫ h, r h*sqrt (radicand μ b r h) ∂μ) ≤
      (∫ h, cost μ β h*(b h^2+r h^2) ∂μ) + (∫ h, multiplier h*r h^2 ∂μ) -
        β^2/(4*(∫ h, multiplier h ∂μ))*
          ((∫ h, b h*v h ∂μ)+(∫ h, v h ∂μ)*(∫ h, b h ∂μ))^2 := by
  let A := ∫ h, b h ∂μ
  let B := ∫ h, b h*v h ∂μ
  let P := fun h => (β^2/4)*(∫ t, (v h+v t)^2*(b t^2+r t^2) ∂μ)/multiplier h
  let N := fun h => (β^2/4)*(B+v h*A)^2/multiplier h
  have hP : Integrable P μ := by
    have hh := (cost_product_integrable β (hb.integrable_sq.add hr.integrable_sq)).integral_prod_left
    have he : P = fun h => ∫ t,
        ((β^2/4)*(v h+v t)^2/multiplier h)*(b t^2+r t^2) ∂μ := by
      funext h
      dsimp [P]
      simp_rw [div_eq_mul_inv]
      rw [←integral_const_mul,←integral_mul_const]
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by ring)
    rw [he]
    exact hh
  have hN : Integrable N μ := integrable_linear_v_cost β A B
  have hmul := integrable_multiplier_square hr
  have hupper : Integrable (fun h => multiplier h*r h^2+P h-N h) μ := (hmul.add hP).sub hN
  have ht := integral_mono ((integrable_radical hb hr).const_mul β) hupper
    (fun h => show β*(r h*sqrt (radicand μ b r h)) ≤ multiplier h*r h^2+P h-N h from by
      have hh := young_radical_pointwise β (r h) (radicand μ b r h) (multiplier h)
        (radicand_nonneg b r h) (multiplier_strict_pos h)
      rw [radicand_expansion hb hr h] at hh ⊢
      dsimp [P,N,A,B]
      convert! hh using 1 <;> ring)
  have hsum : Integrable (fun h => multiplier h*r h^2+P h) μ := hmul.add hP
  rw [integral_const_mul,integral_sub hsum hN,integral_add hmul hP] at ht
  have hpvalue : (∫ h, P h ∂μ) = ∫ h, cost μ β h*(b h^2+r h^2) ∂μ :=
    cost_fubini β (hb.integrable_sq.add hr.integrable_sq)
  rw [hpvalue] at ht
  have hcs := integral_weighted_square (memLp_linear_v A B (μ := μ))
  rw [integral_linear_v] at hcs
  have hnscale : (∫ h, N h ∂μ) = (β^2/4)*(∫ h, (B+v h*A)^2/multiplier h ∂μ) := by
    dsimp [N]
    simp_rw [mul_div_assoc]
    rw [integral_const_mul]
  rw [hnscale] at ht
  have hbound := mul_le_mul_of_nonneg_left hcs (by positivity : 0 ≤ β^2/4)
  have hid : (β^2/4)*((B+(∫ h, v h ∂μ)*A)^2/(∫ h, multiplier h ∂μ)) =
      β^2/(4*(∫ h, multiplier h ∂μ))*(B+(∫ h, v h ∂μ)*A)^2 := by ring
  rw [hid] at hbound
  dsimp [A,B] at hbound
  linarith only [ht,hbound]

end Probability

def variational (β : ℝ) (b r : ℝ → ℝ) : ℝ :=
  (∫ h, diagonal (fieldLaw β) β h*(b h^2+r h^2) ∂fieldLaw β) +
  (∫ h, b h*h ∂fieldLaw β)*(∫ h, b h*v h ∂fieldLaw β) +
  (∫ h, b h ∂fieldLaw β)*(∫ h, b h*(h*v h) ∂fieldLaw β) -
  β^2*(∫ h, b h ∂fieldLaw β)*(∫ h, b h*v h ∂fieldLaw β) +
  2*β^2*(∫ h, b h ∂fieldLaw β)*(∫ h, b h*(m h*v h) ∂fieldLaw β) +
  β^2*(∫ z : ℝ×ℝ, b z.1*kernel z.1 z.2*b z.2 ∂(fieldLaw β).prod (fieldLaw β)) +
  β*(∫ h, r h*sqrt (radicand (fieldLaw β) b r h) ∂fieldLaw β)

def coherent (β : ℝ) (b : ℝ → ℝ) : ℝ :=
  (∫ h, b h*h ∂fieldLaw β)*(∫ h, b h*v h ∂fieldLaw β) +
  (∫ h, b h ∂fieldLaw β)*(∫ h, b h*((h-β^2+2*β^2*m h)*v h) ∂fieldLaw β) +
  β^2*(∫ z : ℝ×ℝ, b z.1*kernel z.1 z.2*b z.2 ∂(fieldLaw β).prod (fieldLaw β)) -
  β^2/(4*(∫ h, multiplier h ∂fieldLaw β))*
    ((∫ h, b h*v h ∂fieldLaw β)+(∫ h, v h ∂fieldLaw β)*(∫ h, b h ∂fieldLaw β))^2

lemma coherent_paired_integrable (β : ℝ) {b : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) :
    Integrable (fun h => b h*((h-β^2+2*β^2*m h)*v h)) (fieldLaw β) := by
  have hco : MemLp (fun h => (h-β^2+2*β^2*m h)*v h) 2 (fieldLaw β) := by
    convert! ((memLp_field_v β).sub (memLp_v.const_mul (β^2))).add
      (memLp_mv.const_mul (2*β^2)) using 1
    ext h
    dsimp
    ring
  exact hb.integrable_mul hco

lemma coherent_paired_expansion (β : ℝ) {b : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) :
    (∫ h, b h*((h-β^2+2*β^2*m h)*v h) ∂fieldLaw β) =
      (∫ h, b h*(h*v h) ∂fieldLaw β)-β^2*(∫ h, b h*v h ∂fieldLaw β) +
        (2*β^2)*(∫ h, b h*(m h*v h) ∂fieldLaw β) := by
  have h1 : Integrable (fun h => b h*(h*v h)) (fieldLaw β) := hb.integrable_mul (memLp_field_v β)
  have h2 : Integrable (fun h => b h*v h) (fieldLaw β) := hb.integrable_mul (memLp_v (p := 2))
  have h3 : Integrable (fun h => b h*(m h*v h)) (fieldLaw β) := hb.integrable_mul (memLp_mv (p := 2))
  have hsub : Integrable (fun h => b h*(h*v h)-β^2*(b h*v h)) (fieldLaw β) := h1.sub (h2.const_mul _)
  have he (h : ℝ) : b h*((h-β^2+2*β^2*m h)*v h) =
      b h*(h*v h)-β^2*(b h*v h)+(2*β^2)*(b h*(m h*v h)) := by ring
  simp_rw [he]
  rw [integral_add hsub (h3.const_mul _),integral_sub h1 (h2.const_mul _),
    integral_const_mul,integral_const_mul]

lemma integrable_diagonal_quadratic (β : ℝ) {b r : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) (hr : MemLp r 2 (fieldLaw β)) :
    Integrable (fun h => diagonal (fieldLaw β) β h*(b h^2+r h^2)) (fieldLaw β) := by
  exact (hb.integrable_sq.add hr.integrable_sq).bdd_mul
    (continuous_diagonal _ β).aestronglyMeasurable
    (ae_of_all _ (fun h => by simpa only [norm_eq_abs] using abs_diagonal_le _ β h))

theorem variational_young (β : ℝ) {b r : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) (hr : MemLp r 2 (fieldLaw β)) :
    variational β b r ≤
      (∫ h, (diagonal (fieldLaw β) β h+cost (fieldLaw β) β h)*(b h^2+r h^2) ∂fieldLaw β) +
      (∫ h, multiplier h*r h^2 ∂fieldLaw β) + coherent β b := by
  have hy := radical_young β hb hr
  have hd := integrable_diagonal_quadratic β hb hr
  have hk := integrable_cost_quadratic β hb hr
  have he : (∫ h, (diagonal (fieldLaw β) β h+cost (fieldLaw β) β h)*(b h^2+r h^2) ∂fieldLaw β) =
      (∫ h, diagonal (fieldLaw β) β h*(b h^2+r h^2) ∂fieldLaw β) +
        (∫ h, cost (fieldLaw β) β h*(b h^2+r h^2) ∂fieldLaw β) := by
    simp_rw [add_mul]
    exact integral_add hd hk
  unfold variational coherent
  rw [he,coherent_paired_expansion β hb]
  nlinarith only [hy]

lemma integrable_total_coefficient (β : ℝ) {b r : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) (hr : MemLp r 2 (fieldLaw β)) :
    Integrable (fun h => (diagonal (fieldLaw β) β h+cost (fieldLaw β) β h+multiplier h)*
      (b h^2+r h^2)) (fieldLaw β) := by
  simp_rw [add_mul,mul_add (multiplier _)]
  exact ((integrable_diagonal_quadratic β hb hr).add (integrable_cost_quadratic β hb hr)).add
    ((integrable_multiplier_square hb).add (integrable_multiplier_square hr))

theorem variational_bound_of_two_estimates (β d c : ℝ) (hc : 0 ≤ c)
    (henvelope : ∀ h, multiplier h+diagonal (fieldLaw β) β h+cost (fieldLaw β) β h ≤ d)
    (hcoherent : ∀ b : ℝ → ℝ, MemLp b 2 (fieldLaw β) →
      coherent β b ≤ ∫ h, (multiplier h+c)*b h^2 ∂fieldLaw β)
    {b r : ℝ → ℝ} (hb : MemLp b 2 (fieldLaw β)) (hr : MemLp r 2 (fieldLaw β))
    (hnorm : (∫ h, b h^2+r h^2 ∂fieldLaw β) = 1) :
    variational β b r ≤ d+c := by
  have hy := variational_young β hb hr
  have hco := hcoherent b hb
  have hsum : Integrable (fun h => (diagonal (fieldLaw β) β h+cost (fieldLaw β) β h)*
      (b h^2+r h^2)) (fieldLaw β) := by
    simp_rw [add_mul]
    exact (integrable_diagonal_quadratic β hb hr).add (integrable_cost_quadratic β hb hr)
  have hDK : Integrable (fun h => diagonal (fieldLaw β) β h*(b h^2+r h^2)+
      cost (fieldLaw β) β h*(b h^2+r h^2)) (fieldLaw β) :=
    (integrable_diagonal_quadratic β hb hr).add (integrable_cost_quadratic β hb hr)
  have hLR : Integrable (fun h => multiplier h*b h^2+multiplier h*r h^2) (fieldLaw β) :=
    (integrable_multiplier_square hb).add (integrable_multiplier_square hr)
  have hexp : (∫ h, (diagonal (fieldLaw β) β h+cost (fieldLaw β) β h+multiplier h)*
      (b h^2+r h^2) ∂fieldLaw β) =
    (∫ h, (diagonal (fieldLaw β) β h+cost (fieldLaw β) β h)*(b h^2+r h^2) ∂fieldLaw β)+
    (∫ h, multiplier h*b h^2 ∂fieldLaw β)+(∫ h, multiplier h*r h^2 ∂fieldLaw β) := by
    simp_rw [add_mul,mul_add (multiplier _)]
    rw [integral_add hDK hLR,
      integral_add (integrable_multiplier_square hb) (integrable_multiplier_square hr)]
    ring
  have hpoint := integral_mono (integrable_total_coefficient β hb hr)
    ((hb.integrable_sq.add hr.integrable_sq).const_mul d)
    (fun h => mul_le_mul_of_nonneg_right (by linarith [henvelope h]) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  simp only [integral_const_mul,Pi.add_apply,hnorm,mul_one,hexp] at hpoint
  have hcb : (∫ h, (multiplier h+c)*b h^2 ∂fieldLaw β) =
    (∫ h, multiplier h*b h^2 ∂fieldLaw β)+c*(∫ h, b h^2 ∂fieldLaw β) := by
    simp_rw [add_mul]
    rw [integral_add (integrable_multiplier_square hb) (hb.integrable_sq.const_mul c),integral_const_mul]
  rw [hcb] at hco
  have hbb : (∫ h, b h^2 ∂fieldLaw β) ≤ 1 := by
    rw [integral_add hb.integrable_sq hr.integrable_sq] at hnorm
    have hn : 0 ≤ ∫ h, r h^2 ∂fieldLaw β := integral_nonneg (fun h => sq_nonneg (r h))
    linarith only [hn,hnorm]
  have hbc := mul_le_mul_of_nonneg_left hbb hc
  nlinarith only [hy,hco,hpoint,hbc]

end SKRatio.Scalar

end

end OAI
