import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityShellPolar
import OAI.Probability.Perceptron.Cavity.CavityShellRestriction
import OAI.Probability.Perceptron.Cavity.CavityExpectedQDrop

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_shell_norm_bound (L : ℕ) (z : {z : Spin L // z∈cavityShell L}) :
    ‖z.val‖≤(L:ℝ)+1 := by
  have hz := z.prop.2
  nlinarith [sq_nonneg (‖z.val‖-1),Nat.cast_nonneg (α:=ℝ) L]

lemma cavityShellProbability_linear_one_le (n k : ℕ)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (Y : Spin (k+1)) :
    1≤∫ z : {z : Spin (k+1) // z∈cavityShell (k+1)},Real.exp (inner ℝ Y z.val)
      ∂cavityShellProbability n (k+1) := by
  have hm : 0<(cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1)) :=
    ENNReal.toReal_pos hp (measure_ne_top _ _)
  have h := cavitySphereLaw_shell_lower n k 0 0 Y (K:=0) (by simp)
  simp only [neg_zero,zero_div,Real.exp_zero,Nat.cast_add,Nat.cast_one,mul_zero,
    add_zero,zero_add,one_mul] at h
  have h1 : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1))≤
      ∫ z in cavityShell (k+1),Real.exp (inner ℝ Y z) ∂(cavitySphereLaw n (k+1) : Measure (Spin (k+1))) := by
    exact (le_mul_of_one_le_right hm.le (one_le_sphericalExp _ _ _)).trans h
  rw [cavityShellProbability_integral n (k+1) (fun z=>Real.exp (inner ℝ Y z))]
  have hh := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hm.le)
  simpa only [inv_mul_cancel₀ hm.ne'] using hh

lemma cavity_true_shell_denominator {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (n k M : ℕ)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (a : S→Fin M→ℝ) (W : S×{z : Spin (k+1) // z∈cavityShell (k+1)}→ℝ)
    (ha : Measurable a) (hW : Measurable W) (t : ℝ) {A C : ℝ}
    (hA : 0≤A) (haB : ∀ s i,|a s i|≤A) (hWB : ∀ p,|W p|≤C)
    (y : Fin M→Spin (k+1)) :
    Real.exp (-C)≤∫ p : S×{z : Spin (k+1) // z∈cavityShell (k+1)},
      Real.exp (W p+cavityLinearField M (k+1) (a p.1) t p.2.val y)
      ∂μ.prod (cavityShellProbability n (k+1)) := by
  have := cavityShellProbability_probability n (k+1) hp
  let F : S×{z : Spin (k+1) // z∈cavityShell (k+1)}→ℝ := fun p=>
    Real.exp (W p+cavityLinearField M (k+1) (a p.1) t p.2.val y)
  have hm : Measurable F := by
    have ha' : Measurable (fun p : S×{z : Spin (k+1) // z∈cavityShell (k+1)} => a p.1) := ha.comp measurable_fst
    unfold F cavityLinearField
    fun_prop
  have hi : Integrable F (μ.prod (cavityShellProbability n (k+1))) := by
    apply Integrable.of_bound hm.aestronglyMeasurable
      (Real.exp (C+|t| *∑ i,A*((k+1:ℕ)+1)*‖y i‖))
    exact ae_of_all _ fun p=>by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact add_le_add (abs_le.mp (hWB p)).2 ((le_abs_self _).trans
        (cavityLinearField_abs_bound M (k+1) (a p.1) t p.2.val y hA (haB p.1)
          (cavity_shell_norm_bound (k+1) p.2)))
  change Real.exp (-C)≤∫ p,F p ∂μ.prod (cavityShellProbability n (k+1))
  rw [integral_prod _ hi]
  apply (show Real.exp (-C)=∫ _ : S,Real.exp (-C) ∂μ by simp).trans_le
  apply integral_mono_ae (integrable_const _) hi.integral_prod_left
  filter_upwards [hi.prod_right_ae] with s hs
  have hlin : Integrable (fun z : {z : Spin (k+1) // z∈cavityShell (k+1)}=>
      Real.exp (cavityLinearField M (k+1) (a s) t z.val y)) (cavityShellProbability n (k+1)) := by
    apply Integrable.of_bound (by unfold cavityLinearField; fun_prop)
      (Real.exp (|t| *∑ i,A*((k+1:ℕ)+1)*‖y i‖))
    exact ae_of_all _ fun z=>by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans
        (cavityLinearField_abs_bound M (k+1) (a s) t z.val y hA (haB s)
          (cavity_shell_norm_bound (k+1) z)))
  calc
    _≤Real.exp (-C)*(∫ z : {z : Spin (k+1) // z∈cavityShell (k+1)},
        Real.exp (cavityLinearField M (k+1) (a s) t z.val y) ∂cavityShellProbability n (k+1)) := by
      apply le_mul_of_one_le_right (Real.exp_pos _).le
      simpa only [cavityLinearField_inner] using
        cavityShellProbability_linear_one_le n k hp (cavityVectorField M (k+1) (a s) t y)
    _≤∫ z,F (s,z) ∂cavityShellProbability n (k+1) := by
      rw [←integral_const_mul]
      apply integral_mono (hlin.const_mul _) hs
      intro z
      dsimp only [F]
      rw [←Real.exp_add]
      exact Real.exp_le_exp.mpr (add_le_add (abs_le.mp (hWB (s,z))).1 le_rfl)

theorem cavity_true_shell_expected_drop {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (n k M : ℕ)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (a b : S→Fin M→ℝ) (W : S×{z : Spin (k+1) // z∈cavityShell (k+1)}→ℝ)
    (ha : Measurable a) (hb : Measurable b) (hW : Measurable W) (t u : ℝ)
    {A B C : ℝ} (hA : 0≤A) (hB : 0≤B) (hC : 0≤C)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B) (hWB : ∀ p,|W p|≤C) :
    (∫ y : Fin M→Spin (k+1),Real.log (∫ p : S×{z : Spin (k+1) // z∈cavityShell (k+1)},
      Real.exp (W p+cavityLinearField M (k+1) (a p.1) t p.2.val y+
        cavityQuadraticField M (k+1) (b p.1) u p.2.val y)
        ∂μ.prod (cavityShellProbability n (k+1))) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))≥
    (∫ y : Fin M→Spin (k+1),Real.log (∫ p : S×{z : Spin (k+1) // z∈cavityShell (k+1)},
      Real.exp (W p+cavityLinearField M (k+1) (a p.1) t p.2.val y)
        ∂μ.prod (cavityShellProbability n (k+1))) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))-
      Real.exp (2*C+t^2*((k+1:ℕ)+1)^2*M*A^2)*
        Real.sqrt (u^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*B^2) := by
  have := cavityShellProbability_probability n (k+1) hp
  exact cavity_expected_log_drop_quadratic (μ.prod (cavityShellProbability n (k+1))) M (k+1)
    (fun p=>a p.1) (fun p=>b p.1) (fun p=>p.2.val) W
    (ha.comp measurable_fst) (hb.comp measurable_fst) (measurable_snd.subtype_val) hW t u
    hA hB hC (by positivity) (fun p=>haB p.1) (fun p=>hbB p.1)
    (fun p=>cavity_shell_norm_bound (k+1) p.2) hWB
    (cavity_true_shell_denominator μ n k M hp a W ha hW t hA haB hWB)


lemma cavity_exp_integrable_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] {H : S→ℝ} (hH : Measurable H)
    {C : ℝ} (hB : ∀ s,|H s|≤C) : Integrable (fun s=>Real.exp (H s)) μ := by
  apply Integrable.of_bound hH.exp.aestronglyMeasurable (Real.exp C)
  exact ae_of_all _ fun s=>by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB s))

lemma cavity_gibbs_log_factorization {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : S→ℝ) (V : S×T→ℝ) (hH : Measurable H) (hV : Measurable V)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hHA : ∀ s,|H s|≤A) (hVB : ∀ p,|V p|≤B) :
    Real.log (∫ p,Real.exp (H p.1+V p) ∂μ.prod ν)-Real.log (∫ s,Real.exp (H s) ∂μ)=
      Real.log (∫ p,Real.exp (V p) ∂(tiltLaw μ H 1).prod ν) := by
  have := tilt_law_probability μ hH hA hHA 1
  have hi : Integrable (fun p : S×T=>Real.exp (H p.1+V p)) (μ.prod ν) := cavity_exp_integrable_bound (μ.prod ν) ((hH.comp measurable_fst).add hV)
    (fun p=>(abs_add_le _ _).trans (add_le_add (hHA p.1) (hVB p)))
  have hj := cavity_exp_integrable_bound ((tiltLaw μ H 1).prod ν) hV hVB
  have hp : 0<∫ s,Real.exp (H s) ∂μ := by
    simpa only [tiltPartition,one_mul] using tilt_partition_pos μ hH hA hHA 1
  have hq : 0<∫ p,Real.exp (V p) ∂(tiltLaw μ H 1).prod ν := by
    simpa only [tiltPartition,one_mul] using tilt_partition_pos ((tiltLaw μ H 1).prod ν) hV hB hVB 1
  have he : (∫ s,Real.exp (H s) ∂μ)*(∫ p,Real.exp (V p) ∂(tiltLaw μ H 1).prod ν)=
      ∫ p,Real.exp (H p.1+V p) ∂μ.prod ν := by
    rw [integral_prod _ hj,tilt_law_integral μ hH hA hHA 1]
    simp only [tiltMean,tiltIntegral,tiltPartition,one_mul]
    rw [mul_div_cancel₀ _ hp.ne',integral_prod _ hi]
    apply integral_congr_ae
    exact ae_of_all _ fun s=>by simp only [Real.exp_add,integral_const_mul]
  rw [←he,Real.log_mul hp.ne' hq.ne']
  ring

theorem cavity_actual_bulk_log_factorization (n L M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (V : CavityShellSpin n L→ℝ) (hV : Measurable V) {B : ℝ}
    (hB : 0≤B) (hVB : ∀ p,|V p|≤B) :
    Real.log (∫ p,Real.exp (bulkHamiltonian (n+1) M f v a.1 a.2 p.1+V p)
      ∂cavityShellBaseLaw n L)-
      bulkLogPartition n M f v a.1 a.2=
    Real.log (∫ p,Real.exp (V p) ∂(tiltLaw (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) 1).prod (cavityShellProbability n L)) := by
  have := cavityShellProbability_probability n L hp
  exact cavity_gibbs_log_factorization (unitSphereLaw (n+1)) (cavityShellProbability n L)
    (bulkHamiltonian (n+1) M f v a.1 a.2) V
    (bulkHamiltonian_section_measurable (n+1) M f v a) hV
    (A:=M*‖f‖+bulkFeatureBound (n+1) v*‖a.2‖)
    (by apply add_nonneg (by positivity); apply mul_nonneg; unfold bulkFeatureBound; positivity; positivity)
    hB (bulkHamiltonian_bound (n+1) M f v a) hVB

end SphericalPerceptronFreeEnergy
end

end OAI
