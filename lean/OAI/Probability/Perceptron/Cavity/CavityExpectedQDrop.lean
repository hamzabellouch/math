import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityUniformRemainder
import OAI.Probability.Perceptron.Cavity.CavitySphericalMoments

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma cavityQuadraticField_abs_bound (M L : ℕ) (b : Fin M→ℝ) (u : ℝ)
    (z : Spin L) (y : Fin M→Spin L) {B D : ℝ} (hB : 0≤B) (hD : 0≤D)
    (hb : ∀ i,|b i|≤B) (hz : ‖z‖≤D) :
    |cavityQuadraticField M L b u z y|≤|u| * ∑ i,B*D^2*(‖y i‖^2+1) := by
  unfold cavityQuadraticField
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul]
  have hkeep : |(inner ℝ z (y i))^2-‖z‖^2|≤D^2*(‖y i‖^2+1) := by
    have hp : (inner ℝ z (y i))^2≤(D*‖y i‖)^2 := by
      apply sq_le_sq.mpr
      simpa only [abs_mul,abs_of_nonneg hD,abs_norm] using
        (abs_real_inner_le_norm z (y i)).trans (mul_le_mul_of_nonneg_right hz (norm_nonneg _))
    have hq : ‖z‖^2≤D^2 := sq_le_sq₀ (norm_nonneg _) hD |>.mpr hz
    calc
      _≤|(inner ℝ z (y i))^2|+|‖z‖^2| := abs_sub _ _
      _=(inner ℝ z (y i))^2+‖z‖^2 := by rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (sq_nonneg _)]
      _≤D^2*(‖y i‖^2+1) := by nlinarith
  exact (mul_le_mul (hb i) hkeep (abs_nonneg _) hB).trans_eq (by ring)

lemma cavity_log_integrable_of_bound {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]
    (μ : Measure S) [IsProbabilityMeasure μ] (P : Measure Y) (H : S×Y→ℝ)
    (hH : Measurable H) (K : Y→ℝ) (hK : Integrable K P)
    (hK0 : ∀ y,0≤K y) (hB : ∀ s y,|H (s,y)|≤K y) :
    Integrable (fun y=>Real.log (∫ s,Real.exp (H (s,y)) ∂μ)) P := by
  have hm : Measurable (fun y=>Real.log (∫ s,Real.exp (H (s,y)) ∂μ)) :=
    hH.exp.stronglyMeasurable.integral_prod_left'.measurable.log
  apply hK.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun y=>by
    rw [Real.norm_eq_abs]
    simpa only [tiltPartition,one_mul,Function.comp_def,id_eq] using tilt_log_partition_bound μ
      (hH.comp (measurable_id.prodMk measurable_const)) (hK0 y) (fun s=>hB s y)

lemma cavity_quadratic_log_integrable {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M L : ℕ)
    (a b : S→Fin M→ℝ) (z : S→Spin L) (W : S→ℝ)
    (ha : Measurable a) (hb : Measurable b) (hz : Measurable z) (hW : Measurable W)
    (t u : ℝ) {A B C D : ℝ} (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B)
    (hzB : ∀ s,‖z s‖≤D) (hWB : ∀ s,|W s|≤C) :
    Integrable (fun y : Fin M→Spin L=>Real.log (∫ s,Real.exp
      (W s+cavityLinearField M L (a s) t (z s) y+cavityQuadraticField M L (b s) u (z s) y) ∂μ))
      (Measure.pi (fun _=>stdGaussian (Spin L))) := by
  let P:=Measure.pi (fun _ : Fin M=>stdGaussian (Spin L))
  let K:=fun y : Fin M→Spin L=>C+|t| *(∑ i,A*D*‖y i‖)+|u| *(∑ i,B*D^2*(‖y i‖^2+1))
  have hi (i : Fin M) (p : ℕ) : Integrable (fun y : Fin M→Spin L=>‖y i‖^p) P :=
    ((measurePreserving_eval (fun _ : Fin M=>stdGaussian (Spin L)) i).integrable_comp
      (cavityNormMoment_integrable L p).aestronglyMeasurable).mpr (cavityNormMoment_integrable L p)
  have hK : Integrable K P := by
    apply Integrable.add
    · apply (integrable_const C).add
      apply Integrable.const_mul
      apply integrable_finsetSum
      intro i _
      simpa only [pow_one] using (hi i 1).const_mul (A*D)
    · apply Integrable.const_mul
      apply integrable_finsetSum
      intro i _
      exact ((hi i 2).add (integrable_const 1)).const_mul (B*D^2)
  apply cavity_log_integrable_of_bound μ P _
    (((hW.comp measurable_fst).add (cavityLinearField_measurable M L a z ha hz t)).add
      (cavityQuadraticField_measurable M L b z hb hz u)) K hK
    (fun y=>by dsimp [K]; positivity)
  intro s y
  apply (abs_add_le _ _).trans
  apply add_le_add _ (cavityQuadraticField_abs_bound M L (b s) u (z s) y hB hD (hbB s) (hzB s))
  exact (abs_add_le _ _).trans (add_le_add (hWB s)
    (cavityLinearField_abs_bound M L (a s) t (z s) y hA (haB s) (hzB s)))

lemma cavity_Q_ratio_integrable {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M L : ℕ)
    (a b : S→Fin M→ℝ) (z : S→Spin L) (W : S→ℝ)
    (ha : Measurable a) (hb : Measurable b) (hz : Measurable z) (hW : Measurable W)
    (t u : ℝ) {A B C D : ℝ} (hA : 0≤A) (hB : 0≤B) (hD : 0≤D)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B)
    (hzB : ∀ s,‖z s‖^2≤D) (hWB : ∀ s,|W s|≤C)
    (hden : ∀ y,Real.exp (-C)≤∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y) ∂μ) :
    Integrable (fun y=>(∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y)*
      |cavityQuadraticField M L (b s) u (z s) y| ∂μ)/(∫ s,Real.exp (W s+
        cavityLinearField M L (a s) t (z s) y) ∂μ))
      (Measure.pi (fun _=>stdGaussian (Spin L))) := by
  have hi:=cavity_Q_product_integrable μ M L a b z W ha hb hz hW t u hA hB hD haB hbB hzB hWB
  have hZ : Measurable (fun y=>∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y) ∂μ) :=
    ((hW.comp measurable_fst).add (cavityLinearField_measurable M L a z ha hz t)).exp.stronglyMeasurable.integral_prod_left'.measurable
  apply (hi.integral_prod_right.const_mul (Real.exp C)).mono'
    (hi.integral_prod_right.aestronglyMeasurable.div₀ hZ.aestronglyMeasurable)
  exact ae_of_all _ fun y=>by
    have hn : 0≤∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y)*
        |cavityQuadraticField M L (b s) u (z s) y| ∂μ :=
      integral_nonneg fun _=>mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
    dsimp only [Pi.div_apply,Pi.mul_apply,Prod.fst,Prod.snd,Function.comp_def]
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hn ((Real.exp_pos _).le.trans (hden y))),
      div_eq_mul_inv,mul_comm (Real.exp C)]
    apply mul_le_mul_of_nonneg_left _ hn
    calc
      _≤(Real.exp (-C))⁻¹ := inv_anti₀ (Real.exp_pos _) (hden y)
      _=Real.exp C := by rw [Real.exp_neg,inv_inv]

theorem cavity_expected_log_drop_quadratic {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M L : ℕ)
    (a b : S→Fin M→ℝ) (z : S→Spin L) (W : S→ℝ)
    (ha : Measurable a) (hb : Measurable b) (hz : Measurable z) (hW : Measurable W)
    (t u : ℝ) {A B C D : ℝ} (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B)
    (hzB : ∀ s,‖z s‖≤D) (hWB : ∀ s,|W s|≤C)
    (hden : ∀ y,Real.exp (-C)≤∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y) ∂μ) :
    (∫ y : Fin M→Spin L,Real.log (∫ s,Real.exp
      (W s+cavityLinearField M L (a s) t (z s) y+cavityQuadraticField M L (b s) u (z s) y) ∂μ)
        ∂Measure.pi (fun _=>stdGaussian (Spin L)))≥
    (∫ y : Fin M→Spin L,Real.log (∫ s,Real.exp
      (W s+cavityLinearField M L (a s) t (z s) y) ∂μ)
        ∂Measure.pi (fun _=>stdGaussian (Spin L)))-
      Real.exp (2*C+t^2*D^2*M*A^2)*
        Real.sqrt (u^2*(D^2)^2*squareGaussianVariance*M*B^2) := by
  let P:=Measure.pi (fun _ : Fin M=>stdGaussian (Spin L))
  let H : S×(Fin M→Spin L)→ℝ:=fun p=>W p.1+cavityLinearField M L (a p.1) t (z p.1) p.2
  let Q : S×(Fin M→Spin L)→ℝ:=fun p=>cavityQuadraticField M L (b p.1) u (z p.1) p.2
  let Z:=fun y=>∫ s,Real.exp (H (s,y)) ∂μ
  let ZQ:=fun y=>∫ s,Real.exp (H (s,y)+Q (s,y)) ∂μ
  let R:=fun y=>(∫ s,Real.exp (H (s,y))*|Q (s,y)| ∂μ)/Z y
  have hsq (s : S) : ‖z s‖^2≤D^2 := pow_le_pow_left₀ (norm_nonneg _) (hzB s) 2
  have hqi : Integrable (fun y=>Real.log (ZQ y)) P :=
    cavity_quadratic_log_integrable μ M L a b z W ha hb hz hW t u hA hB hC hD haB hbB hzB hWB
  have hzi : Integrable (fun y=>Real.log (Z y)) P := by
    simpa only [cavityQuadraticField,zero_mul,add_zero] using
      cavity_quadratic_log_integrable μ M L a b z W ha hb hz hW t 0 hA hB hC hD haB hbB hzB hWB
  have hri : Integrable R P := cavity_Q_ratio_integrable μ M L a b z W ha hb hz hW
    t u hA hB (sq_nonneg D) haB hbB hsq hWB hden
  have hpoint (y : Fin M→Spin L) : Real.log (Z y)-R y≤Real.log (ZQ y) := by
    have hHm : Measurable (fun s=>H (s,y)) :=
      ((hW.comp measurable_fst).add (cavityLinearField_measurable M L a z ha hz t)).comp
        (measurable_id.prodMk measurable_const)
    have hQm : Measurable (fun s=>Q (s,y)) :=
      (cavityQuadraticField_measurable M L b z hb hz u).comp (measurable_id.prodMk measurable_const)
    apply cavity_log_drop_quadratic μ hHm hQm
      (show 0≤C+|t| *∑ i,A*D*‖y i‖ by positivity)
      (show 0≤|u| *∑ i,B*D^2*(‖y i‖^2+1) by positivity)
    · intro s
      exact (abs_add_le _ _).trans (add_le_add (hWB s)
        (cavityLinearField_abs_bound M L (a s) t (z s) y hA (haB s) (hzB s)))
    · intro s
      exact cavityQuadraticField_abs_bound M L (b s) u (z s) y hB hD (hbB s) (hzB s)
  have hmean := integral_mono (hzi.sub hri) hqi hpoint
  simp only [Pi.sub_apply] at hmean
  rw [integral_sub hzi hri] at hmean
  have hcost:=cavity_Q_normalized_bound μ M L a b z W ha hb hz hW t u hA hB
    (sq_nonneg D) haB hbB hsq hWB hden
  exact (sub_le_sub_left hcost _).trans hmean

theorem cavity_angular_expected_log_drop {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M n : ℕ)
    (a b : S→Fin M→ℝ) (R W : S→ℝ) (ha : Measurable a) (hb : Measurable b)
    (hR : Measurable R) (hW : Measurable W) (t u : ℝ)
    {A B C D : ℝ} (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B)
    (hRB : ∀ s,|R s|≤D) (hWB : ∀ s,|W s|≤C) :
    (∫ y : Fin M→Spin (n+1),Real.log (∫ p : S×NormalizedSpin (n+1),Real.exp
      (W p.1+cavityLinearField M (n+1) (a p.1) t (R p.1 •p.2.val) y+
        cavityQuadraticField M (n+1) (b p.1) u (R p.1 •p.2.val) y)
          ∂μ.prod (unitSphereLaw (n+1))) ∂Measure.pi (fun _=>stdGaussian (Spin (n+1))))≥
    (∫ y : Fin M→Spin (n+1),Real.log (∫ p : S×NormalizedSpin (n+1),Real.exp
      (W p.1+cavityLinearField M (n+1) (a p.1) t (R p.1 •p.2.val) y)
          ∂μ.prod (unitSphereLaw (n+1))) ∂Measure.pi (fun _=>stdGaussian (Spin (n+1))))-
      Real.exp (2*C+t^2*D^2*M*A^2)*
        Real.sqrt (u^2*(D^2)^2*squareGaussianVariance*M*B^2) := by
  have hz : Measurable (fun p : S×NormalizedSpin (n+1)=>R p.1 •p.2.val) := by
    have hRm : Measurable (fun p : S×NormalizedSpin (n+1)=>R p.1) := hR.comp measurable_fst
    fun_prop
  have hzB (p : S×NormalizedSpin (n+1)) : ‖R p.1 •p.2.val‖≤D := by
    have hu : ‖p.2.val‖=1 := by simp
    simpa only [norm_smul,Real.norm_eq_abs,hu,mul_one] using hRB p.1
  exact cavity_expected_log_drop_quadratic (μ.prod (unitSphereLaw (n+1))) M (n+1)
    (fun p=>a p.1) (fun p=>b p.1) (fun p=>R p.1 •p.2.val) (fun p=>W p.1)
    (ha.comp measurable_fst) (hb.comp measurable_fst) hz (hW.comp measurable_fst)
    t u hA hB hC hD (fun p=>haB p.1) (fun p=>hbB p.1) hzB (fun p=>hWB p.1)
    (cavity_angular_denominator μ M n a R W ha hR hW t hA haB hRB hWB)

lemma cavity_quadratic_cost_tendsto_zero (M : ℕ→ℕ) (A B C D α : ℝ)
    (hM : Tendsto (fun n=>(M n:ℝ)/(n+1:ℕ)) atTop (𝓝 α)) :
    Tendsto (fun n=>Real.exp (2*C+(1/Real.sqrt (n+1:ℕ))^2*D^2*M n*A^2)*
      Real.sqrt ((1/(2*(n+1:ℕ)))^2*(D^2)^2*squareGaussianVariance*M n*B^2))
        atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hN
  have he := ((hM.mul_const (D^2*A^2)).const_add (2*C)).rexp
  have hq := (((hM.mul hi).mul_const ((D^2)^2*squareGaussianVariance*B^2/4))).sqrt
  have ht := he.mul hq
  simp only [mul_zero,zero_mul,Real.sqrt_zero] at ht
  apply ht.congr'
  filter_upwards [] with n
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  have hs : Real.sqrt (n+1:ℕ)≠0 := (Real.sqrt_pos.mpr hn).ne'
  have hs2 := Real.sq_sqrt hn.le
  congr 2
  · rw [div_pow,one_pow,hs2]
    field_simp
  · field_simp
    ring

end SphericalPerceptronFreeEnergy
end

end OAI
