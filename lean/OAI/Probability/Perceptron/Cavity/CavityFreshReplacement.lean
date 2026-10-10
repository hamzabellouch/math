import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityFiniteEvaluation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavityNormMoment_two (N : ℕ) : cavityNormMoment N 2=N := by
  unfold cavityNormMoment
  rw [←map_pi_eq_stdGaussian,integral_map (by fun_prop) (by fun_prop)]
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp_rw [integral_comp_eval (μ:=fun _ : Fin N=>gaussianReal 0 1)
      (f:=fun y : ℝ=>y^2) (by fun_prop),gaussian_square_mean]
    simp
  · intro i _
    exact ((gaussian_square_memLp_two 1).comp_measurePreserving
      (measurePreserving_eval _ i)).integrable (by norm_num)

lemma cavityNormMoment_one_le (N : ℕ) : cavityNormMoment N 1≤Real.sqrt N := by
  have h := cavity_exp_abs_cauchy (stdGaussian (Spin N))
    (H:=fun _=>0) (Q:=fun y=>‖y‖)
    (by simpa using (memLp_const (1:ℝ) : MemLp (fun _ : Spin N=>(1:ℝ)) 2 (stdGaussian (Spin N))))
    ((IsGaussian.memLp_id (stdGaussian (Spin N)) 2 (by norm_num)).norm)
  simp only [Real.exp_zero,one_mul,abs_of_nonneg (norm_nonneg _),mul_zero,
    integral_const,probReal_univ,smul_eq_mul,Real.sqrt_one] at h
  have he : (∫ y : Spin N,‖y‖^2 ∂stdGaussian (Spin N))=N := cavityNormMoment_two N
  rw [he] at h
  simpa only [cavityNormMoment,pow_one] using h

def cavityFreshMajorant (N L d : ℕ) (f : Jet3)
    (a : Fin d→Fin N→ℝ) (y : Fin d→Spin L) : ℝ :=
  ‖f.d1‖*∑ i,(((L:ℝ)+1)/(N+L:ℕ)*‖WithLp.toLp 2 (a i)‖+
    ((L:ℝ)+1)/Real.sqrt (N+L:ℕ)*‖y i‖)

lemma cavity_fresh_pattern_error (n L : ℕ) (f : Jet3) (a : Fin (n+1)→ℝ)
    (y : Spin L) (s : CavityShellSpin n L) :
    |f.f (cavityRho (n+1) L s.2.val*(∑ j,a j*s.1.val j)+
      inner ℝ s.2.val y/Real.sqrt (n+1+L:ℕ))-f.f (∑ j,a j*s.1.val j)|≤
    ‖f.d1‖*(((L:ℝ)+1)/(n+1+L:ℕ)*‖WithLp.toLp 2 a‖+
      ((L:ℝ)+1)/Real.sqrt (n+1+L:ℕ)*‖y‖) := by
  have hp : (0:ℝ)<(n+1+L:ℕ) := by positivity
  have hz := s.2.prop.2
  have hD : ‖s.2.val‖^2≤(n+1+L:ℕ) := by
    simp only [Nat.cast_add,Nat.cast_one] at *
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hr := cavityRho_bounds (n+1) L s.2.val (by omega) hD
  have hz1 : ‖s.2.val‖≤(L:ℝ)+1 := by
    nlinarith [sq_nonneg (‖s.2.val‖-1),Nat.cast_nonneg (α:=ℝ) L]
  have hx : ‖s.1.val‖=1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using s.1.prop
  have ha : |∑ j,a j*s.1.val j|≤‖WithLp.toLp 2 a‖ := by
    have hi := abs_real_inner_le_norm s.1.val (WithLp.toLp 2 a)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      starRingEnd_apply,star_trivial,PiLp.toLp_apply,hx,one_mul] using hi
  have hi : |inner ℝ s.2.val y|≤((L:ℝ)+1)*‖y‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hz1 (norm_nonneg _))
  have hl := f.lipschitz.dist_le_mul
    (cavityRho (n+1) L s.2.val*(∑ j,a j*s.1.val j)+inner ℝ s.2.val y/Real.sqrt (n+1+L:ℕ))
    (∑ j,a j*s.1.val j)
  simp only [Real.dist_eq,coe_nnnorm] at hl
  apply hl.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [show cavityRho (n+1) L s.2.val*(∑ j,a j*s.1.val j)+inner ℝ s.2.val y/Real.sqrt (n+1+L:ℕ)-
    (∑ j,a j*s.1.val j)=(cavityRho (n+1) L s.2.val-1)*(∑ j,a j*s.1.val j)+
    inner ℝ s.2.val y/Real.sqrt (n+1+L:ℕ) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_div,abs_of_pos (Real.sqrt_pos.mpr hp),abs_of_nonpos (sub_nonpos.mpr hr.2.1)]
  apply add_le_add
  · have hb := hr.2.2.trans (div_le_div_of_nonneg_right hz hp.le)
    exact mul_le_mul (by simpa only [neg_sub] using hb) ha (abs_nonneg _) (by positivity)
  · simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hi (Real.sqrt_nonneg _)

lemma cavity_fresh_pattern_sum_error (n L d : ℕ) (f : Jet3)
    (a : Fin d→Fin (n+1)→ℝ) (y : Fin d→Spin L) (s : CavityShellSpin n L) :
    |cavityShellPatternEnergy n L d f.f (cavityJoinedPatterns (n+1) L d a y) s-
      normalizedPatternEnergy (n+1) d f.f a s.1|≤cavityFreshMajorant (n+1) L d f a y := by
  rw [cavityShellPatternEnergy_join]
  unfold normalizedPatternEnergy cavityFreshMajorant
  rw [←Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  simpa only [cavityRho,Nat.cast_add,Nat.cast_one] using cavity_fresh_pattern_error n L f (a i) (y i) s

lemma cavity_fresh_log_replacement (n L d : ℕ) (f : Jet3)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (H : CavityShellSpin n L→ℝ) (hH : Measurable H) {A : ℝ}
    (hA : 0≤A) (hHA : ∀ s,|H s|≤A)
    (a : Fin d→Fin (n+1)→ℝ) (y : Fin d→Spin L) :
    |Real.log (∫ s,Real.exp (H s+cavityShellPatternEnergy n L d f.f
        (cavityJoinedPatterns (n+1) L d a y) s) ∂cavityShellBaseLaw n L)-
      Real.log (∫ s,Real.exp (H s+normalizedPatternEnergy (n+1) d f.f a s.1)
        ∂cavityShellBaseLaw n L)|≤cavityFreshMajorant (n+1) L d f a y := by
  let := cavityShellBaseLaw_probability n L hp
  have hnew := cavityShellPatternEnergy_measurable n L d f.f
    (cavityJoinedPatterns (n+1) L d a y)
  have hold : Measurable (fun s : CavityShellSpin n L=>normalizedPatternEnergy (n+1) d f.f a s.1) := by
    unfold normalizedPatternEnergy
    have hc := f.f.continuous.measurable
    fun_prop
  apply cavity_log_uniform_change (cavityShellBaseLaw n L) (hH.add hnew) (hH.add hold)
    (A:=A+d*‖f.f‖) (add_nonneg hA (by positivity))
  · intro s
    exact (abs_add_le _ _).trans (add_le_add (hHA s) (cavityShellPatternEnergy_bound n L d f.f _ s))
  · intro s
    simpa only [Pi.add_apply,add_sub_add_left_eq_sub] using cavity_fresh_pattern_sum_error n L d f a y s

lemma cavity_row_norm_integrable (d L : ℕ) :
    Integrable (fun y : Fin d→Spin L=>∑ i,‖y i‖) (Measure.pi (fun _=>stdGaussian (Spin L))) := by
  apply integrable_finsetSum
  intro i hi
  simpa only [pow_one,Function.comp_def,Function.eval] using ((measurePreserving_eval (fun _ : Fin d=>stdGaussian (Spin L)) i).integrable_comp_of_integrable
    (cavityNormMoment_integrable L 1))

lemma cavity_row_norm_mean (d L : ℕ) :
    (∫ y : Fin d→Spin L,∑ i,‖y i‖ ∂Measure.pi (fun _=>stdGaussian (Spin L)))=
      d*cavityNormMoment L 1 := by
  rw [integral_finsetSum]
  · simp_rw [integral_comp_eval (μ:=fun _ : Fin d=>stdGaussian (Spin L))
      (f:=fun y : Spin L=>‖y‖) (by fun_prop)]
    simp [cavityNormMoment]
  · intro i hi
    simpa only [pow_one,Function.comp_def,Function.eval] using ((measurePreserving_eval (fun _ : Fin d=>stdGaussian (Spin L)) i).integrable_comp_of_integrable
      (cavityNormMoment_integrable L 1))

lemma cavityFreshMajorant_integrable (N L d : ℕ) (f : Jet3) :
    Integrable (fun p : (Fin d→Spin N)×(Fin d→Spin L)=>
      cavityFreshMajorant N L d f (fun i=>WithLp.ofLp (p.1 i)) p.2)
      ((Measure.pi (fun _=>stdGaussian (Spin N))).prod (Measure.pi (fun _=>stdGaussian (Spin L)))) := by
  simp only [cavityFreshMajorant,WithLp.toLp_ofLp,Finset.sum_add_distrib,←Finset.mul_sum]
  exact ((((cavity_row_norm_integrable d N).comp_fst (Measure.pi (fun _ : Fin d=>stdGaussian (Spin L)))).const_mul _).add
    (((cavity_row_norm_integrable d L).comp_snd (Measure.pi (fun _ : Fin d=>stdGaussian (Spin N)))).const_mul _)).const_mul _

lemma cavityFreshMajorant_mean (N L d : ℕ) (f : Jet3) :
    (∫ p : (Fin d→Spin N)×(Fin d→Spin L),
      cavityFreshMajorant N L d f (fun i=>WithLp.ofLp (p.1 i)) p.2
      ∂(Measure.pi (fun _=>stdGaussian (Spin N))).prod (Measure.pi (fun _=>stdGaussian (Spin L))))=
      ‖f.d1‖*d*(((L:ℝ)+1)/(N+L:ℕ)*cavityNormMoment N 1+
        ((L:ℝ)+1)/Real.sqrt (N+L:ℕ)*cavityNormMoment L 1) := by
  simp only [cavityFreshMajorant,WithLp.toLp_ofLp,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [integral_const_mul,integral_add
    (((cavity_row_norm_integrable d N).comp_fst (Measure.pi (fun _ : Fin d=>stdGaussian (Spin L)))).const_mul _)
    (((cavity_row_norm_integrable d L).comp_snd (Measure.pi (fun _ : Fin d=>stdGaussian (Spin N)))).const_mul _)]
  simp only [integral_const_mul]
  rw [integral_fun_fst (fun a : Fin d→Spin N=>∑ i,‖a i‖),
    integral_fun_snd (fun y : Fin d→Spin L=>∑ i,‖y i‖)]
  simp only [probReal_univ,one_smul,cavity_row_norm_mean]
  ring

lemma cavityFreshMajorant_mean_bound (n L d : ℕ) (f : Jet3) :
    (∫ p : (Fin d→Spin (n+1))×(Fin d→Spin L),
      cavityFreshMajorant (n+1) L d f (fun i=>WithLp.ofLp (p.1 i)) p.2
      ∂(Measure.pi (fun _=>stdGaussian (Spin (n+1)))).prod (Measure.pi (fun _=>stdGaussian (Spin L))))≤
      ‖f.d1‖*d*((L:ℝ)+1)*(1+Real.sqrt L)/Real.sqrt (n+1:ℕ) := by
  rw [cavityFreshMajorant_mean]
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  have hnL : ((n+1:ℕ):ℝ)≤(n+1+L:ℕ) := by exact_mod_cast Nat.le_add_right (n+1) L
  have ha : ((L:ℝ)+1)/(n+1+L:ℕ)*cavityNormMoment (n+1) 1≤
      ((L:ℝ)+1)/Real.sqrt (n+1:ℕ) := by
    calc
      _≤((L:ℝ)+1)/(n+1+L:ℕ)*Real.sqrt (n+1:ℕ) :=
        mul_le_mul_of_nonneg_left (cavityNormMoment_one_le _) (by positivity)
      _≤((L:ℝ)+1)/(n+1:ℕ)*Real.sqrt (n+1:ℕ) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) hn hnL) (Real.sqrt_nonneg _)
      _=((L:ℝ)+1)/Real.sqrt (n+1:ℕ) := by
        rw [div_mul_eq_mul_div,mul_div_assoc,Real.sqrt_div_self']
        ring
  have hb : ((L:ℝ)+1)/Real.sqrt (n+1+L:ℕ)*cavityNormMoment L 1≤
      ((L:ℝ)+1)/Real.sqrt (n+1:ℕ)*Real.sqrt L := by
    exact (mul_le_mul_of_nonneg_left (cavityNormMoment_one_le L) (by positivity)).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hn) (Real.sqrt_le_sqrt hnL))
        (Real.sqrt_nonneg _))
  apply (mul_le_mul_of_nonneg_left (add_le_add ha hb) (by positivity : 0≤‖f.d1‖*(d:ℝ))).trans_eq
  ring

lemma cavityFreshMajorant_mean_tendsto (D L : ℕ) (d : ℕ→ℕ) (hd : ∀ n,d n≤D) (f : Jet3) :
    Tendsto (fun n=>∫ p : (Fin (d n)→Spin (n+1))×(Fin (d n)→Spin L),
      cavityFreshMajorant (n+1) L (d n) f (fun i=>WithLp.ofLp (p.1 i)) p.2
      ∂(Measure.pi (fun _=>stdGaussian (Spin (n+1)))).prod (Measure.pi (fun _=>stdGaussian (Spin L))))
      atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hs := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN)
  have ht := hs.const_mul (‖f.d1‖*D*((L:ℝ)+1)*(1+Real.sqrt L))
  simp only [mul_zero] at ht
  apply squeeze_zero (fun n=>?_) (fun n=>?_) ht
  · apply integral_nonneg
    intro p
    unfold cavityFreshMajorant
    positivity
  · apply (cavityFreshMajorant_mean_bound n L (d n) f).trans
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hd n) (norm_nonneg _)

end SphericalPerceptronFreeEnergy
end

end OAI
