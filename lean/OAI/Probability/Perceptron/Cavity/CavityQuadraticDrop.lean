import Mathlib
import OAI.Probability.Perceptron.Variational.LocalMaxSecondDerivNonpos
import OAI.Probability.Perceptron.Brownian.CavityGaussianFields

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

lemma cavity_log_drop_quadratic {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {H Q : S→ℝ}
    (hH : Measurable H) (hQ : Measurable Q) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hHA : ∀ x,|H x|≤A) (hQB : ∀ x,|Q x|≤B) :
    Real.log (∫ x,Real.exp (H x+Q x) ∂μ)≥
      Real.log (∫ x,Real.exp (H x) ∂μ)-
        (∫ x,Real.exp (H x)*|Q x| ∂μ)/(∫ x,Real.exp (H x) ∂μ) := by
  have hc := affineLogRoot_convex μ hH hQ hA hB hHA hQB
  have hd := affineLogRoot_deriv μ hH hQ hA hB hHA hQB 0
  have hs := hc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) (by norm_num : (0:ℝ)<1) hd
  simp only [affineLogRoot,tiltPartition,slope,zero_mul,add_zero,one_mul,sub_zero,inv_one,one_smul,vsub_eq_sub] at hs
  have hqq : -(∫ x,Real.exp (H x)*|Q x| ∂μ)≤∫ x,Real.exp (H x)*Q x ∂μ := by
    rw [←integral_neg]
    apply integral_mono
    · have hi : Integrable (fun x=>Real.exp (H x)*|Q x|) μ := by
        simpa only [one_mul] using tilt_integrable μ hH hQ.abs hA hB hHA (fun x=>by simpa only [abs_abs] using hQB x) 1
      exact hi.neg
    · simpa only [one_mul] using tilt_integrable μ hH hQ hA hB hHA hQB 1
    · intro x
      have := mul_le_mul_of_nonneg_left (neg_abs_le (Q x)) (Real.exp_pos (H x)).le
      simpa only [mul_neg] using this
  have hp : 0<∫ x,Real.exp (H x) ∂μ := by
    simpa only [tiltPartition,one_mul] using tilt_partition_pos μ hH hA hHA 1
  have hdiv := (div_le_div_of_nonneg_right hqq hp.le)
  simp only [tiltMean,tiltIntegral,tiltPartition,one_mul] at hs
  rw [neg_div] at hdiv
  linarith

lemma cavity_exp_abs_cauchy {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {H Q : Ω→ℝ} (hE : MemLp (fun y=>Real.exp (H y)) 2 P) (hQ : MemLp Q 2 P) :
    (∫ y,Real.exp (H y)*|Q y| ∂P)≤
      Real.sqrt (∫ y,Real.exp (2*H y) ∂P)*Real.sqrt (∫ y,(Q y)^2 ∂P) := by
  have hp : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have he := integral_mul_norm_le_Lp_mul_Lq hp (by simpa using hE) (by simpa using hQ)
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.rpow_two, sq_abs] at he
  simp_rw [←Real.exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat] at he
  simpa only [Real.sqrt_eq_rpow,one_div] using he

lemma cavityLinearField_exp_integrable (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) (p : ℝ) :
    Integrable (fun y=>Real.exp (p*cavityLinearField M L a t z y))
      (Measure.pi (fun _=>stdGaussian (Spin L))) := by
  by_contra hi
  have h:=cavityLinearField_exp_moment M L a t z p
  rw [integral_undef hi] at h
  exact (Real.exp_pos _).ne' h.symm

lemma cavityLinearField_exp_memLp (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) (p : ℝ) :
    MemLp (fun y=>Real.exp (p*cavityLinearField M L a t z y)) 2
      (Measure.pi (fun _=>stdGaussian (Spin L))) := by
  apply (memLp_two_iff_integrable_sq (show AEStronglyMeasurable
    (fun y=>Real.exp (p*cavityLinearField M L a t z y)) _ from
      (show Continuous (fun y=>Real.exp (p*cavityLinearField M L a t z y)) from by
        unfold cavityLinearField; fun_prop).aestronglyMeasurable)).mpr
  have hi:=cavityLinearField_exp_integrable M L a t z (2*p)
  convert hi using 1
  ext y
  rw [←Real.exp_nat_mul]
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

lemma cavity_tilted_Q_conditional (M L : ℕ) (a b : Fin M→ℝ) (t u : ℝ) (z : Spin L) :
    (∫ y,Real.exp (cavityLinearField M L a t z y)*|cavityQuadraticField M L b u z y|
      ∂Measure.pi (fun _=>stdGaussian (Spin L)))≤
      Real.exp (t^2*‖z‖^2*∑ i,(a i)^2)*
        Real.sqrt (u^2*‖z‖^4*squareGaussianVariance*∑ i,(b i)^2) := by
  have he : MemLp (fun y=>Real.exp (cavityLinearField M L a t z y)) 2
      (Measure.pi (fun _=>stdGaussian (Spin L))) := by
    simpa only [one_mul] using cavityLinearField_exp_memLp M L a t z 1
  have h:=cavity_exp_abs_cauchy _ he (cavityQuadraticField_memLp M L b u z)
  rw [cavityLinearField_exp_moment,cavityQuadraticField_second_moment] at h
  have hx : (2:ℝ)^2*t^2*‖z‖^2/2*(∑ i,(a i)^2)=2*(t^2*‖z‖^2*∑ i,(a i)^2) := by ring
  have he2 (r : ℝ) : Real.exp (2*r)=(Real.exp r)^2 := Real.exp_nat_mul r 2
  rw [hx,he2,Real.sqrt_sq (Real.exp_pos _).le] at h
  exact h

lemma cavity_tilted_Q_uniform (M L : ℕ) (a b : Fin M→ℝ) (t u : ℝ) (z : Spin L)
    {A B D : ℝ} (_hA : 0≤A) (_hB : 0≤B) (hD : 0≤D)
    (ha : ∀ i,|a i|≤A) (hb : ∀ i,|b i|≤B) (hz : ‖z‖^2≤D) :
    (∫ y,Real.exp (cavityLinearField M L a t z y)*|cavityQuadraticField M L b u z y|
      ∂Measure.pi (fun _=>stdGaussian (Spin L)))≤
      Real.exp (t^2*D*M*A^2)*Real.sqrt (u^2*D^2*squareGaussianVariance*M*B^2) := by
  have hs {c : Fin M→ℝ} {C : ℝ} (hc : ∀ i, |c i|≤C) : ∑ i,(c i)^2≤M*C^2 := by
    calc
      _≤∑ _ : Fin M,C^2 := Finset.sum_le_sum fun i _=>by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (c i)) (hc i) 2
      _=_ := by simp
  apply (cavity_tilted_Q_conditional M L a b t u z).trans
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    calc
      _≤t^2*D*(M*A^2) := mul_le_mul
        (mul_le_mul_of_nonneg_left hz (sq_nonneg t)) (hs ha)
        (Finset.sum_nonneg fun _ _=>sq_nonneg _) (mul_nonneg (sq_nonneg t) hD)
      _=_ := by ring
  · apply Real.sqrt_le_sqrt
    calc
      _=u^2*(‖z‖^2)^2*squareGaussianVariance*(∑ i,(b i)^2) := by ring
      _≤u^2*D^2*squareGaussianVariance*(M*B^2) := mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (sq_nonneg _) hz 2) (sq_nonneg _)) squareGaussianVariance_nonneg)
        (hs hb) (Finset.sum_nonneg fun _ _=>sq_nonneg _)
        (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) squareGaussianVariance_nonneg)
      _=_ := by ring
  · exact Real.sqrt_nonneg _
  · exact (Real.exp_pos _).le

lemma cavity_tilted_Q_integrable (M L : ℕ) (a b : Fin M→ℝ) (t u : ℝ) (z : Spin L) :
    Integrable (fun y=>Real.exp (cavityLinearField M L a t z y)*|cavityQuadraticField M L b u z y|)
      (Measure.pi (fun _=>stdGaussian (Spin L))) := by
  have he : MemLp (fun y=>Real.exp (cavityLinearField M L a t z y)) 2
      (Measure.pi (fun _=>stdGaussian (Spin L))) := by
    simpa only [one_mul] using cavityLinearField_exp_memLp M L a t z 1
  exact he.integrable_mul (cavityQuadraticField_memLp M L b u z).abs

lemma cavityLinearField_measurable {S : Type*} [MeasurableSpace S] (M L : ℕ)
    (a : S→Fin M→ℝ) (z : S→Spin L) (ha : Measurable a) (hz : Measurable z) (t : ℝ) :
    Measurable (fun p : S×(Fin M→Spin L)=>cavityLinearField M L (a p.1) t (z p.1) p.2) := by
  unfold cavityLinearField
  have hac : Measurable (fun p : S×(Fin M→Spin L)=>a p.1) := ha.comp measurable_fst
  have hzc : Measurable (fun p : S×(Fin M→Spin L)=>z p.1) := hz.comp measurable_fst
  fun_prop

lemma cavityQuadraticField_measurable {S : Type*} [MeasurableSpace S] (M L : ℕ)
    (b : S→Fin M→ℝ) (z : S→Spin L) (hb : Measurable b) (hz : Measurable z) (u : ℝ) :
    Measurable (fun p : S×(Fin M→Spin L)=>cavityQuadraticField M L (b p.1) u (z p.1) p.2) := by
  unfold cavityQuadraticField
  have hbc : Measurable (fun p : S×(Fin M→Spin L)=>b p.1) := hb.comp measurable_fst
  have hzc : Measurable (fun p : S×(Fin M→Spin L)=>z p.1) := hz.comp measurable_fst
  fun_prop

lemma cavity_Q_product_integrable {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M L : ℕ)
    (a b : S→Fin M→ℝ) (z : S→Spin L) (W : S→ℝ)
    (ha : Measurable a) (hb : Measurable b) (hz : Measurable z) (hW : Measurable W)
    (t u : ℝ) {A B C D : ℝ} (hA : 0≤A) (hB : 0≤B) (hD : 0≤D)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B)
    (hzB : ∀ s,‖z s‖^2≤D) (hWB : ∀ s,|W s|≤C) :
    Integrable (fun p : S×(Fin M→Spin L)=>Real.exp (W p.1+cavityLinearField M L (a p.1) t (z p.1) p.2)*
      |cavityQuadraticField M L (b p.1) u (z p.1) p.2|)
      (μ.prod (Measure.pi (fun _=>stdGaussian (Spin L)))) := by
  let P:=Measure.pi (fun _ : Fin M=>stdGaussian (Spin L))
  let F : S×(Fin M→Spin L)→ℝ:=fun p=>
    Real.exp (W p.1+cavityLinearField M L (a p.1) t (z p.1) p.2)*
      |cavityQuadraticField M L (b p.1) u (z p.1) p.2|
  have hm : Measurable F :=
    ((hW.comp measurable_fst).add (cavityLinearField_measurable M L a z ha hz t)).exp.mul
      (cavityQuadraticField_measurable M L b z hb hz u).abs
  have hf s : Integrable (fun y=>F (s,y)) P := by
    simpa only [F,Real.exp_add,mul_assoc] using
      (cavity_tilted_Q_integrable M L (a s) (b s) t u (z s)).const_mul (Real.exp (W s))
  have hbound s : (∫ y,F (s,y) ∂P)≤Real.exp C*
      (Real.exp (t^2*D*M*A^2)*Real.sqrt (u^2*D^2*squareGaussianVariance*M*B^2)) := by
    conv_lhs => simp only [F,Real.exp_add,mul_assoc,integral_const_mul]
    exact mul_le_mul (Real.exp_le_exp.mpr (abs_le.mp (hWB s)).2)
      (cavity_tilted_Q_uniform M L (a s) (b s) t u (z s) hA hB hD (haB s) (hbB s) (hzB s))
      (integral_nonneg fun _=>mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) (Real.exp_pos _).le
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hf,?_⟩
  apply Integrable.of_bound (hm.aestronglyMeasurable.norm.integral_prod_right')
    (Real.exp C*(Real.exp (t^2*D*M*A^2)*Real.sqrt (u^2*D^2*squareGaussianVariance*M*B^2)))
  filter_upwards [] with s
  have hp : ∀ y,0≤F (s,y) := fun y=>mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  simp only [Real.norm_eq_abs]
  simp_rw [abs_of_nonneg (hp _)]
  rw [abs_of_nonneg (integral_nonneg hp)]
  exact hbound s

lemma cavity_Q_normalized_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M L : ℕ)
    (a b : S→Fin M→ℝ) (z : S→Spin L) (W : S→ℝ)
    (ha : Measurable a) (hb : Measurable b) (hz : Measurable z) (hW : Measurable W)
    (t u : ℝ) {A B C D : ℝ} (hA : 0≤A) (hB : 0≤B) (hD : 0≤D)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B)
    (hzB : ∀ s,‖z s‖^2≤D) (hWB : ∀ s,|W s|≤C)
    (hden : ∀ y,Real.exp (-C)≤∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y) ∂μ) :
    (∫ y,(∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y)*
        |cavityQuadraticField M L (b s) u (z s) y| ∂μ)/
      (∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y) ∂μ)
      ∂Measure.pi (fun _=>stdGaussian (Spin L)))≤
      Real.exp (2*C+t^2*D*M*A^2)*Real.sqrt (u^2*D^2*squareGaussianVariance*M*B^2) := by
  let P:=Measure.pi (fun _ : Fin M=>stdGaussian (Spin L))
  let F : S×(Fin M→Spin L)→ℝ:=fun p=>
    Real.exp (W p.1+cavityLinearField M L (a p.1) t (z p.1) p.2)*
      |cavityQuadraticField M L (b p.1) u (z p.1) p.2|
  let Z : (Fin M→Spin L)→ℝ:=fun y=>∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y) ∂μ
  have hi : Integrable F (μ.prod P) := cavity_Q_product_integrable μ M L a b z W ha hb hz hW t u hA hB hD haB hbB hzB hWB
  have hZm : AEStronglyMeasurable Z P := by
    exact (((hW.comp measurable_fst).add (cavityLinearField_measurable M L a z ha hz t)).exp.stronglyMeasurable).integral_prod_left'.aestronglyMeasurable
  have hnorm y : 0≤∫ s,F (s,y) ∂μ := integral_nonneg fun _=>mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hratio y : (∫ s,F (s,y) ∂μ)/Z y≤Real.exp C*(∫ s,F (s,y) ∂μ) := by
    rw [div_eq_mul_inv,mul_comm (Real.exp C)]
    apply mul_le_mul_of_nonneg_left _ (hnorm y)
    calc
      (Z y)⁻¹≤(Real.exp (-C))⁻¹ := inv_anti₀ (Real.exp_pos _) (hden y)
      _=Real.exp C := by rw [Real.exp_neg,inv_inv]
  have hrI : Integrable (fun y=>(∫ s,F (s,y) ∂μ)/Z y) P := by
    apply (hi.integral_prod_right.const_mul (Real.exp C)).mono'
      (hi.integral_prod_right.aestronglyMeasurable.div₀ hZm)
    filter_upwards [] with y
    change ‖(∫ s,F (s,y) ∂μ)/Z y‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (hnorm y) ((Real.exp_pos _).le.trans (hden y)))]
    exact hratio y
  calc
    _≤∫ y,Real.exp C*(∫ s,F (s,y) ∂μ) ∂P := integral_mono hrI (hi.integral_prod_right.const_mul _) hratio
    _=Real.exp C*(∫ s,∫ y,F (s,y) ∂P ∂μ) := by
      rw [integral_const_mul,←integral_integral_swap hi]
    _≤Real.exp C*(Real.exp C*(Real.exp (t^2*D*M*A^2)*Real.sqrt (u^2*D^2*squareGaussianVariance*M*B^2))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      calc
        _≤∫ _ : S,Real.exp C*(Real.exp (t^2*D*M*A^2)*Real.sqrt (u^2*D^2*squareGaussianVariance*M*B^2)) ∂μ := by
          apply integral_mono hi.integral_prod_left (integrable_const _)
          intro s
          conv_lhs => simp only [F,Real.exp_add,mul_assoc,integral_const_mul]
          exact mul_le_mul (Real.exp_le_exp.mpr (abs_le.mp (hWB s)).2)
            (cavity_tilted_Q_uniform M L (a s) (b s) t u (z s) hA hB hD (haB s) (hbB s) (hzB s))
            (integral_nonneg fun _=>mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) (Real.exp_pos _).le
        _=_ := by simp
    _=_ := by
      have he : Real.exp (2*C)=(Real.exp C)^2 := Real.exp_nat_mul C 2
      rw [Real.exp_add,he]
      ring

end SphericalPerceptronFreeEnergy
end

end OAI
