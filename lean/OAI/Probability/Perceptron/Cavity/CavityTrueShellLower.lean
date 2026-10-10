import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityTrueShellQ

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_sphericalExp_bound (k : ℕ) (Y : Spin (k+1)) (R : ℝ) :
    sphericalExp k Y R≤Real.exp (|R| *‖Y‖) := by
  simpa [sphericalExp] using sphericalExp_le_mul k R Y 0

lemma cavity_shell_compensator_bound (k : ℕ) (W C K A : ℝ)
    (hK : 0≤K) (hC : |C|≤K) (hW : |W|≤A)
    (z : {z : Spin (k+1) // z∈cavityShell (k+1)}) :
    |W+‖z.val‖^2*C/2|≤A+((k+1:ℕ)+1)*K/2 := by
  apply (abs_add_le _ _).trans
  apply add_le_add hW
  rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg _)]
  norm_num
  apply div_le_div_of_nonneg_right _ (by norm_num)
  simpa only [Nat.cast_add,Nat.cast_one] using
    ((mul_le_mul_of_nonneg_left hC (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_right z.prop.2 hK))

theorem cavity_true_shell_linear_lower {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (n k : ℕ)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (W C : S→ℝ) (Y : S→Spin (k+1))
    (hW : Measurable W) (hC : Measurable C) (hY : Measurable Y)
    {A K D : ℝ} (hA : 0≤A) (hK : 0≤K) (hD : 0≤D)
    (hWA : ∀ s,|W s|≤A) (hCK : ∀ s,|C s|≤K) (hYD : ∀ s,‖Y s‖≤D) :
    Real.log (∫ s,Real.exp (W s+(k+1:ℕ)*C s/2)*
      sphericalExp k (Y s) (Real.sqrt (k+1:ℕ)) ∂μ)-K/2≤
    Real.log (∫ p : S×{z : Spin (k+1) // z∈cavityShell (k+1)},
      Real.exp (W p.1+‖p.2.val‖^2*C p.1/2+inner ℝ (Y p.1) p.2.val)
        ∂μ.prod (cavityShellProbability n (k+1))) := by
  have := cavityShellProbability_probability n (k+1) hp
  let R : ℝ:=Real.sqrt (k+1:ℕ)
  let G : S→ℝ:=fun s=>Real.exp (W s+(k+1:ℕ)*C s/2)*sphericalExp k (Y s) R
  let F : S×{z : Spin (k+1) // z∈cavityShell (k+1)}→ℝ:=fun p=>
    Real.exp (W p.1+‖p.2.val‖^2*C p.1/2+inner ℝ (Y p.1) p.2.val)
  have hbase (s : S) : |W s+(k+1:ℕ)*C s/2|≤A+(k+1:ℕ)*K/2 := by
    apply (abs_add_le _ _).trans
    apply add_le_add (hWA s)
    rw [abs_div,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hCK s) (by positivity)) (by norm_num)
  have hgm : Measurable G :=
    ((hW.add ((hC.const_mul _).div_const _)).exp).mul
      ((sphericalExp_continuous k R).measurable.comp hY)
  have hgi : Integrable G μ := by
    apply Integrable.of_bound hgm.aestronglyMeasurable (Real.exp (A+(k+1:ℕ)*K/2+R*D))
    exact ae_of_all _ fun s=>by
      dsimp [G]
      rw [abs_mul,abs_of_pos (Real.exp_pos _),
        abs_of_nonneg ((show (0:ℝ)≤1 by norm_num).trans (one_le_sphericalExp _ _ _)),Real.exp_add (A+(k+1:ℕ)*K/2) (R*D)]
      apply mul_le_mul
        (Real.exp_le_exp.mpr ((le_abs_self _).trans (hbase s)))
        ((cavity_sphericalExp_bound k (Y s) R).trans (Real.exp_le_exp.mpr _))
        ((by norm_num : (0:ℝ)≤1).trans (one_le_sphericalExp _ _ _)) (Real.exp_pos _).le
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hYD s) (Real.sqrt_nonneg _)
  have hfm : Measurable F := by
    dsimp [F]
    fun_prop
  have hfb (p : S×{z : Spin (k+1) // z∈cavityShell (k+1)}) :
      |W p.1+‖p.2.val‖^2*C p.1/2+inner ℝ (Y p.1) p.2.val|≤
        A+((k+1:ℕ)+1)*K/2+D*((k+1:ℕ)+1) := by
    apply (abs_add_le _ _).trans
    apply add_le_add (cavity_shell_compensator_bound k _ _ _ _ hK (hCK p.1) (hWA p.1) p.2)
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hYD p.1) (cavity_shell_norm_bound (k+1) p.2) (norm_nonneg _) hD)
  have hfi : Integrable F (μ.prod (cavityShellProbability n (k+1))) :=
    cavity_exp_integrable_bound _ (by fun_prop) hfb
  have hgp : 0<∫ s,G s ∂μ := by
    have hbi := cavity_exp_integrable_bound μ (by fun_prop) hbase
    have hpos : 0<∫ s,Real.exp (W s+(k+1:ℕ)*C s/2) ∂μ := by
      simpa only [tiltPartition,one_mul] using tilt_partition_pos μ (v:=fun s=>W s+(k+1:ℕ)*C s/2)
        (hW.add ((hC.const_mul _).div_const _)) (by positivity) hbase 1
    apply hpos.trans_le (integral_mono hbi hgi _)
    intro s
    exact le_mul_of_one_le_right (Real.exp_pos _).le (one_le_sphericalExp _ _ _)
  have hpoint (s : S) : Real.exp (-K/2)*G s≤
      ∫ z,F (s,z) ∂cavityShellProbability n (k+1) := by
    rw [show (∫ z,F (s,z) ∂cavityShellProbability n (k+1))=
      ((cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1)))⁻¹*
        ∫ z in cavityShell (k+1),Real.exp (W s+‖z‖^2*C s/2+inner ℝ (Y s) z)
          ∂(cavitySphereLaw n (k+1) : Measure (Spin (k+1))) from
      cavityShellProbability_integral n (k+1) (fun z=>Real.exp (W s+‖z‖^2*C s/2+inner ℝ (Y s) z))]
    have hm : 0<(cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1)) :=
      ENNReal.toReal_pos hp (measure_ne_top _ _)
    have hh:=mul_le_mul_of_nonneg_left
      (cavitySphereLaw_shell_lower n k (W s) (C s) (Y s) (hCK s)) (inv_nonneg.mpr hm.le)
    simpa only [G,R,←mul_assoc,inv_mul_cancel₀ hm.ne',one_mul] using hh
  have hcompare : Real.exp (-K/2)*(∫ s,G s ∂μ)≤∫ p,F p ∂μ.prod (cavityShellProbability n (k+1)) := by
    rw [←integral_const_mul,integral_prod _ hfi]
    exact integral_mono (hgi.const_mul _) hfi.integral_prod_left hpoint
  have hlog:=Real.log_le_log (mul_pos (Real.exp_pos _) hgp) hcompare
  rw [Real.log_mul (Real.exp_pos _).ne' hgp.ne',Real.log_exp] at hlog
  change Real.log (∫ s,G s ∂μ)-K/2≤Real.log (∫ p,F p ∂μ.prod (cavityShellProbability n (k+1)))
  linarith


lemma cavityVectorField_norm_le (M L : ℕ) (a : Fin M→ℝ) (t : ℝ)
    (y : Fin M→Spin L) {A : ℝ} (hA : 0≤A) (ha : ∀ i,|a i|≤A) :
    ‖cavityVectorField M L a t y‖≤|t| *∑ i,A*‖y i‖ := by
  unfold cavityVectorField
  rw [norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul (ha i) le_rfl (norm_nonneg _) hA

lemma cavity_angular_partition {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M k : ℕ)
    (a : S→Fin M→ℝ) (V : S→ℝ) (ha : Measurable a) (hV : Measurable V)
    (t R : ℝ) {A C : ℝ} (hA : 0≤A) (hC : 0≤C)
    (haB : ∀ s i,|a s i|≤A) (hVB : ∀ s,|V s|≤C) (y : Fin M→Spin (k+1)) :
    (∫ p : S×NormalizedSpin (k+1),Real.exp (V p.1+
      cavityLinearField M (k+1) (a p.1) t (R •p.2.val) y) ∂μ.prod (unitSphereLaw (k+1)))=
    ∫ s,Real.exp (V s)*sphericalExp k (cavityVectorField M (k+1) (a s) t y) R ∂μ := by
  have hm : Measurable (fun p : S×NormalizedSpin (k+1)=>V p.1+
      cavityLinearField M (k+1) (a p.1) t (R •p.2.val) y) := by
    have ham : Measurable (fun p : S×NormalizedSpin (k+1)=>a p.1) := ha.comp measurable_fst
    have hVm : Measurable (fun p : S×NormalizedSpin (k+1)=>V p.1) := hV.comp measurable_fst
    unfold cavityLinearField
    fun_prop
  have hi := cavity_exp_integrable_bound (μ.prod (unitSphereLaw (k+1))) hm
    (C:=|C|+|t| *∑ i,A*|R| *‖y i‖) (fun p=>by
      rw [abs_of_nonneg hC]
      apply (abs_add_le _ _).trans
      apply add_le_add (hVB p.1)
      apply cavityLinearField_abs_bound M (k+1) (a p.1) t _ y hA (haB p.1)
      have hu : ‖p.2.val‖=1 := by simp
      simp only [norm_smul,Real.norm_eq_abs,hu,mul_one,le_refl])
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun s=>by
    simp only [cavityLinearField_inner,real_inner_smul_right,Real.exp_add,integral_const_mul,sphericalExp]

lemma cavity_angular_log_integrable {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M k : ℕ)
    (a : S→Fin M→ℝ) (V : S→ℝ) (ha : Measurable a) (hV : Measurable V)
    (t R : ℝ) {A C : ℝ} (hA : 0≤A) (hC : 0≤C)
    (haB : ∀ s i,|a s i|≤A) (hVB : ∀ s,|V s|≤C) :
    Integrable (fun y : Fin M→Spin (k+1)=>Real.log (∫ s,Real.exp (V s)*
      sphericalExp k (cavityVectorField M (k+1) (a s) t y) R ∂μ))
        (Measure.pi (fun _=>stdGaussian (Spin (k+1)))) := by
  have hz : Measurable (fun p : S×NormalizedSpin (k+1)=>R •p.2.val) := by fun_prop
  have hzB (p : S×NormalizedSpin (k+1)) : ‖R •p.2.val‖≤|R| := by
    have hu : ‖p.2.val‖=1 := by simp
    simp only [norm_smul,Real.norm_eq_abs,hu,mul_one,le_refl]
  have h:=cavity_quadratic_log_integrable (μ.prod (unitSphereLaw (k+1))) M (k+1)
    (fun p=>a p.1) (fun _ _=>0) (fun p=>R •p.2.val) (fun p=>V p.1)
    (ha.comp measurable_fst) measurable_const hz (hV.comp measurable_fst) t 0
    hA (B:=0) (by norm_num) hC (abs_nonneg R)
    (fun p=>haB p.1) (fun _ _=>by simp) hzB (fun p=>hVB p.1)
  simp only [cavityQuadraticField,zero_mul,add_zero] at h
  simpa only [cavity_angular_partition μ M k a V ha hV t R hA hC haB hVB] using h

theorem cavity_expected_shell_lower {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (n k M : ℕ)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (a b : S→Fin M→ℝ) (W C : S→ℝ)
    (ha : Measurable a) (hb : Measurable b) (hW : Measurable W) (hC : Measurable C)
    (t u : ℝ) {A B E K : ℝ} (hA : 0≤A) (hB : 0≤B) (hE : 0≤E) (hK : 0≤K)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B)
    (hWE : ∀ s,|W s|≤E) (hCK : ∀ s,|C s|≤K) :
    (∫ y : Fin M→Spin (k+1),Real.log (∫ p : S×{z : Spin (k+1) // z∈cavityShell (k+1)},
      Real.exp (W p.1+‖p.2.val‖^2*C p.1/2+cavityLinearField M (k+1) (a p.1) t p.2.val y+
        cavityQuadraticField M (k+1) (b p.1) u p.2.val y)
        ∂μ.prod (cavityShellProbability n (k+1))) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))≥
    (∫ y : Fin M→Spin (k+1),Real.log (∫ s,Real.exp (W s+(k+1:ℕ)*C s/2)*
      sphericalExp k (cavityVectorField M (k+1) (a s) t y) (Real.sqrt (k+1:ℕ)) ∂μ)
      ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))-K/2-
      Real.exp (2*(E+((k+1:ℕ)+1)*K/2)+t^2*((k+1:ℕ)+1)^2*M*A^2)*
        Real.sqrt (u^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*B^2) := by
  have := cavityShellProbability_probability n (k+1) hp
  let U : S×{z : Spin (k+1) // z∈cavityShell (k+1)}→ℝ := fun p=>W p.1+‖p.2.val‖^2*C p.1/2
  have hU : Measurable U := by
    have hmW : Measurable (fun p : S×{z : Spin (k+1) // z∈cavityShell (k+1)}=>W p.1) := hW.comp measurable_fst
    have hmC : Measurable (fun p : S×{z : Spin (k+1) // z∈cavityShell (k+1)}=>C p.1) := hC.comp measurable_fst
    dsimp [U]
    fun_prop
  have hUB (p) : |U p|≤E+((k+1:ℕ)+1)*K/2 :=
    cavity_shell_compensator_bound k _ _ _ _ hK (hCK p.1) (hWE p.1) p.2
  have hdrop:=cavity_true_shell_expected_drop μ n k M hp a b U ha hb hU t u
    hA hB (by positivity) haB hbB hUB
  have hlin : Integrable (fun y : Fin M→Spin (k+1)=>Real.log (∫ p,
      Real.exp (U p+cavityLinearField M (k+1) (a p.1) t p.2.val y)
      ∂μ.prod (cavityShellProbability n (k+1)))) (Measure.pi (fun _=>stdGaussian (Spin (k+1)))) := by
    simpa only [cavityQuadraticField,zero_mul,add_zero] using
      cavity_quadratic_log_integrable (μ.prod (cavityShellProbability n (k+1))) M (k+1)
        (fun p=>a p.1) (fun p=>b p.1) (fun p=>p.2.val) U
        (ha.comp measurable_fst) (hb.comp measurable_fst) measurable_snd.subtype_val hU t 0
        hA hB (by positivity) (by positivity) (fun p=>haB p.1) (fun p=>hbB p.1)
        (fun p=>cavity_shell_norm_bound (k+1) p.2) hUB
  have hVB (s) : |W s+(k+1:ℕ)*C s/2|≤E+(k+1:ℕ)*K/2 := by
    apply (abs_add_le _ _).trans
    apply add_le_add (hWE s)
    rw [abs_div,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hCK s) (by positivity)) (by norm_num)
  have hsph:=cavity_angular_log_integrable μ M k a (fun s=>W s+(k+1:ℕ)*C s/2)
    ha (hW.add ((hC.const_mul _).div_const _)) t (Real.sqrt (k+1:ℕ)) hA (by positivity) haB hVB
  have hcomp:=integral_mono (hsph.sub (integrable_const (K/2))) hlin (fun y=>by
    have hym : Measurable (fun s=>cavityVectorField M (k+1) (a s) t y) := by
      unfold cavityVectorField
      fun_prop
    have h:=cavity_true_shell_linear_lower μ n k hp W C _ hW hC hym hE hK
      (D:=|t| *∑ i,A*‖y i‖) (by positivity) hWE hCK
      (fun s=>cavityVectorField_norm_le M (k+1) (a s) t y hA (haB s))
    simpa only [Pi.sub_apply,U,cavityLinearField_inner] using h)
  simp only [Pi.sub_apply] at hcomp
  rw [integral_sub hsph (integrable_const (K/2)),integral_const,probReal_univ,smul_eq_mul,one_mul] at hcomp
  exact (sub_le_sub_right hcomp _).trans hdrop

end SphericalPerceptronFreeEnergy
end

end OAI
