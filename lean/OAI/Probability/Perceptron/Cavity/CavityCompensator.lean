import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityBulkLog

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_exp_local_lipschitz {a b K : ℝ} (ha : a≤K) (hb : b≤K) :
    |Real.exp a-Real.exp b|≤Real.exp K*|a-b| := by
  have h:=Convex.norm_image_sub_le_of_norm_deriv_le
    (f:=Real.exp) (s:=Iic K) (C:=Real.exp K)
    (fun x _hx=>Real.differentiableAt_exp)
    (fun x hx=>by simpa only [Real.deriv_exp,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx)
    (convex_Iic K) hb ha
  simpa only [Real.norm_eq_abs] using h

lemma cavity_log_local_lipschitz {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a-Real.log b|≤|a-b|/m := by
  have h:=Convex.norm_image_sub_le_of_norm_deriv_le
    (f:=Real.log) (s:=Ici m) (C:=m⁻¹)
    (fun x hx=>Real.differentiableAt_log (hm.trans_le hx).ne')
    (fun x hx=>by
      rw [Real.deriv_log,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hm.trans_le hx))]
      exact inv_anti₀ hm hx)
    (convex_Ici m) hb ha
  simpa only [Real.norm_eq_abs,div_eq_mul_inv,mul_comm] using h

lemma cavity_compensator_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {W C : S→ℝ} {a b K c t : ℝ}
    (hW : Measurable W) (hC : Measurable C) (ha : 0<a) (ht : 0≤t)
    (hw : ∀ x,a≤W x ∧ W x≤b) (hc : |c|≤K) (hcb : ∀ x,|C x|≤K) :
    |Real.log (∫ x,Real.exp (t*C x)*W x ∂μ)-
      (t*c+Real.log (∫ x,W x ∂μ))|≤
      (Real.exp (t*K)*b/(Real.exp (-(t*K))*a))*t*(∫ x,|C x-c| ∂μ) := by
  have hb : 0≤b := by
    by_contra hh
    have hfalse : ∀ x : S, False := fun x=>not_le.mpr (ha.trans_le ((hw x).1.trans (hw x).2)) (le_of_not_ge hh)
    have he : (univ : Set S)=∅ := Set.ext (fun x=>⟨fun _=>(hfalse x).elim,fun h=>h.elim⟩)
    have hμ := measure_univ (μ:=μ)
    rw [he,measure_empty] at hμ
    exact zero_ne_one hμ
  have hK : 0≤K := (abs_nonneg c).trans hc
  have hWi : Integrable W μ := Integrable.of_bound hW.aestronglyMeasurable b
    (ae_of_all _ fun x=>by rw [Real.norm_eq_abs,abs_of_pos (ha.trans_le (hw x).1)]; exact (hw x).2)
  have hEi : Integrable (fun x=>Real.exp (t*C x)*W x) μ :=
    Integrable.of_bound (hC.const_mul t |>.exp |>.aestronglyMeasurable |>.mul hW.aestronglyMeasurable)
      (Real.exp (t*K)*b) (ae_of_all _ fun x=>by
        rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (ha.trans_le (hw x).1)]
        exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hcb x)).2 ht))
          (hw x).2 (ha.trans_le (hw x).1).le (Real.exp_pos _).le)
  have hBi := hWi.const_mul (Real.exp (t*c))
  have hlo : Real.exp (-(t*K))*a≤∫ x,Real.exp (t*C x)*W x ∂μ := by
    calc
      _=∫ _ : S,Real.exp (-(t*K))*a ∂μ := by simp
      _≤_ := integral_mono (integrable_const _) hEi fun x=>by
        apply mul_le_mul _ (hw x).1 ha.le (Real.exp_pos _).le
        apply Real.exp_le_exp.mpr
        nlinarith [(abs_le.mp (hcb x)).1]
  have hWlo : a≤∫ x,W x ∂μ := by
    simpa using integral_mono (integrable_const a) hWi fun x=>(hw x).1
  have hbLo : Real.exp (-(t*K))*a≤Real.exp (t*c)*(∫ x,W x ∂μ) := by
    apply mul_le_mul _ hWlo ha.le (Real.exp_pos _).le
    exact Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp hc).1])
  have hCi : Integrable (fun x=>|C x-c|) μ :=
    Integrable.of_bound (hC.sub_const c).abs.aestronglyMeasurable (K+|c|)
      (ae_of_all _ fun x=>by simpa only [Real.norm_eq_abs,abs_abs] using
        (abs_sub (C x) c).trans (add_le_add (hcb x) (le_refl |c|)))
  have hdiff : |(∫ x,Real.exp (t*C x)*W x ∂μ)-Real.exp (t*c)*(∫ x,W x ∂μ)|≤
      Real.exp (t*K)*b*t*(∫ x,|C x-c| ∂μ) := by
    rw [←integral_const_mul,←integral_sub hEi hBi]
    apply (abs_integral_le_integral_abs).trans
    rw [←integral_const_mul]
    apply integral_mono (hEi.sub hBi).abs (hCi.const_mul _)
    intro x
    simp only [Pi.sub_apply]
    rw [←sub_mul,abs_mul,abs_of_pos (ha.trans_le (hw x).1)]
    have hex:=cavity_exp_local_lipschitz
      (mul_le_mul_of_nonneg_left (abs_le.mp (hcb x)).2 ht)
      (mul_le_mul_of_nonneg_left (abs_le.mp hc).2 ht)
    rw [←mul_sub,abs_mul,abs_of_nonneg ht] at hex
    calc
      _≤(Real.exp (t*K)*(t*|C x-c|))*b := mul_le_mul hex (hw x).2 (ha.trans_le (hw x).1).le (by positivity)
      _=_ := by ring
  have hlog:=cavity_log_local_lipschitz (mul_pos (Real.exp_pos _) ha) hlo hbLo
  rw [Real.log_mul (Real.exp_pos _).ne' (ha.trans_le hWlo).ne',Real.log_exp] at hlog
  exact hlog.trans (by
    apply (div_le_div_of_nonneg_right hdiff (mul_pos (Real.exp_pos _) ha).le).trans
    apply le_of_eq
    ring)


lemma bulkC_measurable (m M : ℕ) (f : Jet3) :
    Measurable (fun p : BulkDisorder (m+1) M×NormalizedSpin (m+1)=>bulkC (m+1) M f p.1.1 p.2) := by
  unfold bulkC
  fun_prop

lemma bulkC_bound (m M : ℕ) (f : Jet3) (hf : HasCompactSupport (f.d1 : ℝ→ℝ))
    (a : BulkDisorder (m+1) M) (x : NormalizedSpin (m+1)) :
    |bulkC (m+1) M f a.1 x|≤M/(m+1:ℕ)*‖f.dilationMark hf‖ := by
  exact bulkSingleAverage_bound m M (f.dilationMark hf) a (fun _=>x)

def cavityBulkCompPartition (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) : ℝ :=
  tiltMean (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v p.1)
    (fun x=>Real.exp ((n+1:ℕ)/2*bulkC (m+1) M f p.1.1 x)*
      cavitySingleTest n d f.f Λ hΛ (gaussianRows (cavityBulkFeature n d m M f p.1 x) p.2)) 1

lemma cavity_comp_partition_joint_measurable {A S J E : Type*}
    [MeasurableSpace A] [MeasurableSpace S] [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) [SFinite μ]
    (v : A→S→J→E) (hv : Measurable (Function.uncurry v))
    (H C : A→S→ℝ) (hH : Measurable (Function.uncurry H))
    (hC : Measurable (Function.uncurry C)) (t : ℝ) (Ψ : EuclideanSpace ℝ J→ᵇℝ) :
    Measurable (fun p : A×E=>tiltMean μ (H p.1)
      (fun x=>Real.exp (t*C p.1 x)*Ψ (gaussianRows (v p.1 x) p.2)) 1) := by
  let κ : Kernel (A×E) S := Kernel.const _ μ
  have hproj : Measurable (fun p : (A×E)×S=>(p.1.1,p.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  apply kernel_tiltMean_measurable κ (H:=fun p x=>H p.1 x)
    (Y:=fun p x=>Real.exp (t*C p.1 x)*Ψ (gaussianRows (v p.1 x) p.2)) (hH.comp hproj)
  exact ((hC.comp hproj).const_mul t).exp.mul
    (Ψ.measurable.comp (cavity_rows_joint_measurable (hv.comp hproj) measurable_fst.snd))

lemma cavityBulkCompPartition_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) : Measurable (cavityBulkCompPartition n d m M f v Λ hΛ) := by
  exact cavity_comp_partition_joint_measurable (unitSphereLaw (m+1))
    (cavityBulkFeature n d m M f) (cavityBulkFeature_measurable n d m M f)
    (bulkGibbsHamiltonian m M f.f v) (fun a x=>bulkC (m+1) M f a.1 x)
    (bulkGibbsHamiltonian_measurable m M f.f v) (bulkC_measurable m M f) _ _

def cavityCompensatorConstant (n d : ℕ) (f : ℝ→ᵇℝ) (Λ K : ℝ) : ℝ :=
  (Real.exp ((n+1:ℕ)/2*K)*(Λ*Real.exp ((d:ℝ)*‖f‖))/
    (Real.exp (-((n+1:ℕ)/2*K))*Real.exp (-(d:ℝ)*‖f‖)))*((n+1:ℕ)/2)

lemma cavityCompensatorConstant_nonneg (n d : ℕ) (f : ℝ→ᵇℝ) {Λ K : ℝ} (hΛ : 1≤Λ) :
    0≤cavityCompensatorConstant n d f Λ K := by
  unfold cavityCompensatorConstant
  have : 0≤Λ := (by norm_num : (0:ℝ)≤1).trans hΛ
  positivity

lemma tilt_cavity_compensator_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {H W C : S→ℝ} {a b K c t : ℝ}
    (hH : Measurable H) (he : Integrable (fun x=>Real.exp (1*H x)) μ)
    (hW : Measurable W) (hC : Measurable C) (ha : 0<a) (ht : 0≤t)
    (hw : ∀ x,a≤W x ∧ W x≤b) (hc : |c|≤K) (hcb : ∀ x,|C x|≤K) :
    |Real.log (tiltMean μ H (fun x=>Real.exp (t*C x)*W x) 1)-
      (t*c+Real.log (tiltMean μ H W 1))|≤
      (Real.exp (t*K)*b/(Real.exp (-(t*K))*a))*t*(tiltMean μ H (fun x=>|C x-c|) 1) := by
  have := tilt_law_probability_of_integrable μ he
  simp_rw [←tilt_law_integral_of_integrable μ hH he]
  exact cavity_compensator_bound _ hW hC ha ht hw hc hcb

lemma cavityBulkSingleWeight_measurable (n d m M : ℕ) (f : Jet3)
    (Λ : ℝ) (hΛ : 1≤Λ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    Measurable (fun x=>cavitySingleTest n d f.f Λ hΛ
      (gaussianRows (cavityBulkFeature n d m M f p.1 x) p.2)) := by
  exact (cavitySingleTest n d f.f Λ hΛ).measurable.comp
    (cavity_rows_joint_measurable ((cavityBulkFeature_measurable n d m M f).of_uncurry_left) measurable_const)

lemma cavityBulkCompPartition_error (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c K : ℝ) (hc : |c|≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤K)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    |Real.log (cavityBulkCompPartition n d m M f v Λ hΛ p)-
      ((n+1:ℕ)/2*c+Real.log (cavityBulkPartition n d m M f v Λ hΛ p))|≤
    cavityCompensatorConstant n d f.f Λ K*
      tiltMean (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v p.1)
        (fun x=>|bulkC (m+1) M f p.1.1 x-c|) 1 := by
  apply tilt_cavity_compensator_bound (unitSphereLaw (m+1))
    ((bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left)
    (by simpa only [one_mul,bulkGibbsHamiltonian] using bulkHamiltonian_exp_integrable m M f.f v p.1)
    (cavityBulkSingleWeight_measurable n d m M f Λ hΛ p)
    ((bulkC_measurable m M f).comp (measurable_const.prodMk measurable_id))
    (Real.exp_pos _) (by positivity) (fun x=>cavitySingleTest_bounds n d f.f Λ hΛ _) hc (hC p.1)

lemma bulkC_L1_of_L2 (N M : ℕ→ℕ) (f : Jet3) (hf : HasCompactSupport (f.d1 : ℝ→ℝ))
    (v : ℕ→ℕ→ℝ) (c : ℝ)
    (hc : Tendsto (fun j=>bulkReplicaMean (N j) (M j) f.f (v j) 1
      (fun a x=>(bulkC (N j+1) (M j) f a.1 (x 0)-c)^2)) atTop (𝓝 0)) :
    Tendsto (fun j=>bulkReplicaMean (N j) (M j) f.f (v j) 1
      (fun a x=>|bulkC (N j+1) (M j) f a.1 (x 0)-c|)) atTop (𝓝 0) := by
  apply bulkReplicaMean_L2_tendsto N M f.f v 1
    (fun j a x=>|bulkC (N j+1) (M j) f a.1 (x 0)-c|)
    (fun j=>?_) (fun j=>(M j:ℝ)/(N j+1:ℕ)*‖f.dilationMark hf‖+|c|)
    (fun j=>by positivity) (fun j a x=>?_) 0
  · simpa only [sub_zero,sq_abs] using hc
  · exact (((bulkC_measurable (N j) (M j) f).comp
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).sub_const c).abs
  · rw [abs_abs]
    exact (abs_sub _ _).trans (add_le_add (bulkC_bound (N j) (M j) f hf a (x 0)) le_rfl)

end SphericalPerceptronFreeEnergy
end

end OAI
