import Mathlib
import OAI.Probability.Perceptron.Variational.Field
import OAI.Probability.Perceptron.Cavity.CavityShellSubexp
import OAI.Probability.Perceptron.Cavity.CavityGoodFreshLower

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma block_increment_linear_lower (F : ℕ→ℝ) {L : ℕ} (hL : 0<L) {q : ℝ}
    (hq : ∀ᶠ n : ℕ in atTop,q≤F (n+L)-F n) :
    ∃ C : ℝ,∀ n : ℕ,(n:ℝ)*(q/L)-C≤F n := by
  obtain ⟨N,hN⟩:=eventually_atTop.1 hq
  have hb : BddAbove (Set.range (fun i : Fin (N+L)=>(i.val:ℝ)*(q/L)-F i.val)) :=
    (Set.finite_range _).bddAbove
  obtain ⟨C,hC⟩:=hb
  refine ⟨C,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<N+L
    · have hh:=hC (Set.mem_range_self (⟨n,hn⟩ : Fin (N+L)))
      dsimp at hh
      linarith
    · have hm : N≤n-L:=by omega
      have hml : n-L<n:=by omega
      have he : n-L+L=n:=by omega
      have hi:=ih (n-L) hml
      have ha:=hN (n-L) hm
      rw [he] at ha
      have hc : ((n-L:ℕ):ℝ)+(L:ℝ)=(n:ℝ) := by exact_mod_cast he
      have hlr : (L:ℝ)≠0 := by positivity
      have hr : (L:ℝ)*(q/L)=q := mul_div_cancel₀ q hlr
      have hr' : (n:ℝ)*(q/L)=((n-L:ℕ):ℝ)*(q/L)+q := by rw [←hc,add_mul,hr]
      rw [hr']
      linarith

lemma block_increment_asymptotic_lower (F : ℕ→ℝ) {L : ℕ} (hL : 0<L) {q : ℝ}
    (hq : ∀ᶠ n : ℕ in atTop,q≤F (n+L)-F n) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop,q/L-δ≤F n/(n+1:ℕ) := by
  obtain ⟨C,hC⟩:=block_increment_linear_lower F hL hq
  have ht : Tendsto (fun n : ℕ=>(C+q/L)/(n+1:ℕ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,one_mul,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (C+q/L)
  filter_upwards [ht.eventually (Iio_mem_nhds hδ)] with n hn
  have hp : (0:ℝ)<(n+1:ℕ) := by positivity
  apply (le_div_iff₀ hp).mpr
  have he : (C+q/L)<δ*(n+1:ℕ) := (div_lt_iff₀ hp).mp hn
  have hh:=hC n
  push_cast at *
  nlinarith

lemma cavity_averaged_log_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,(terminalVariational P α g.f).toReal-ε≤
      cavityAveragedLog α g.f n/(n+1:ℕ) := by
  obtain ⟨G⟩:=exists_cavityGoodParameters hα.le g.f
  let V:=(terminalVariational P α g.f).toReal
  let C:=α*‖g.dilationMark h1‖/2+‖g.f‖+1
  have ht : Tendsto (fun k : ℕ=>Real.log (cavityShellMass k)/(k+1:ℕ)-C/(k+1:ℕ)) atTop (𝓝 0) := by
    have hc : Tendsto (fun k : ℕ=>C/(k+1:ℕ)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,one_mul,mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul C
    simpa only [sub_zero] using cavityShell_log_sublinear.sub hc
  obtain ⟨k,hk,hc⟩:=((cavity_averaged_increment_good P hB hα g h1 h2 h3 G
    (show 0<ε/3 by positivity)).and
    (ht.eventually (Ioi_mem_nhds (show -ε/3<0 by linarith)))).exists
  have hi:=hk 1 (by norm_num)
  let q:=Real.log (cavityShellMass k)-α*‖g.dilationMark h1‖/2+
    (k+1:ℕ)*(V-ε/3)-‖g.f‖-1
  have hq : q/(k+1:ℕ)>V-2*ε/3 := by
    have hp : (0:ℝ)<(k+1:ℕ):=by positivity
    have he : q/(k+1:ℕ)=V-ε/3+
        (Real.log (cavityShellMass k)/(k+1:ℕ)-C/(k+1:ℕ)) := by
      dsimp [q,C]
      field_simp
      ring
    rw [he]
    linarith
  filter_upwards [block_increment_asymptotic_lower (cavityAveragedLog α g.f)
    (Nat.succ_pos k) (q:=q) hi (show 0<ε/3 by positivity)] with n hn
  change V-ε≤_
  linarith


lemma normalizedPatternLog_integrable (n M : ℕ) (f : ℝ→ᵇℝ) :
    Integrable (normalizedPatternLog n M f) (finitePatternRowsLaw (n+1) M) := by
  apply Integrable.of_bound (normalizedPatternLog_measurable n M f).aestronglyMeasurable (M*‖f‖)
  filter_upwards [] with a
  rw [Real.norm_eq_abs]
  simpa only [normalizedPatternLog,tiltPartition,one_mul,Function.comp_apply,id_eq] using
    tilt_log_partition_bound (unitSphereLaw (n+1))
    ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp (measurable_const.prodMk measurable_id))
    (by positivity : 0≤M*‖f‖) (normalizedPatternEnergy_bound _ _ _ a)

lemma bulkExpectedLog_unperturbed_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    |bulkExpectedLog n M f v-∫ a,normalizedPatternLog n M f a ∂finitePatternRowsLaw (n+1) M|≤
      Real.pi*bulkFeatureBound (n+1) v^2 := by
  have hj:=cavity_gaussian_joint_log_integrable (finitePatternRowsLaw (n+1) M)
    (unitSphereLaw (n+1)) (normalizedPatternEnergy (n+1) M f) (bulkFeature (n+1) v)
    (normalizedPatternEnergy_continuous (n+1) M f).measurable
    (bulkFeature_continuous (n+1) v).measurable
    (by positivity : 0≤M*‖f‖) (Real.sqrt_nonneg _)
    (normalizedPatternEnergy_bound _ _ _)
    (fun x=>(bulkFeature_norm _ _ _).le)
  have hp (a : Fin M→Fin (n+1)→ℝ) :
      |(∫ z,Real.log (tiltPartition (unitSphereLaw (n+1))
        (fun x=>normalizedPatternEnergy (n+1) M f a x+inner ℝ (bulkFeature (n+1) v x) z) 1)
        ∂stdGaussian (BulkMark (n+1)))-normalizedPatternLog n M f a|≤
      Real.pi*bulkFeatureBound (n+1) v^2 := by
    have h:=independentGaussian_covariance_comparison (unitSphereLaw (n+1))
      (V:=fun _=>(0:BulkMark (n+1)))
      ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp (measurable_const.prodMk measurable_id))
      measurable_const (bulkFeature_continuous (n+1) v).measurable
      (by positivity : 0≤M*‖f‖) (Real.sqrt_nonneg _)
      (normalizedPatternEnergy_bound _ _ _ a)
      (fun _=>by simp) (fun x=>(bulkFeature_norm _ _ _).le)
      (sq_nonneg (bulkFeatureBound (n+1) v)) (fun x y=>by
        simp only [inner_zero_left,sub_zero]
        simpa only [bulkFeature_norm,pow_two] using abs_real_inner_le_norm (bulkFeature (n+1) v x) (bulkFeature (n+1) v y))
    simpa only [inner_zero_left,add_zero,integral_const,probReal_univ,one_smul,
      tiltPartition,one_mul,normalizedPatternLog,Function.comp_apply,id_eq] using h
  have hJ : Integrable (fun a : Fin M→Fin (n+1)→ℝ=>∫ z,Real.log
      (tiltPartition (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a z) 1)
      ∂stdGaussian (BulkMark (n+1))) (finitePatternRowsLaw (n+1) M) := hj.integral_prod_left
  rw [bulkExpectedLog_nested,←integral_sub hJ (normalizedPatternLog_integrable n M f)]
  apply (abs_integral_le_integral_abs).trans
  calc
    (∫ a,|((∫ z,Real.log (tiltPartition (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a z) 1) ∂stdGaussian (BulkMark (n+1)))-
      normalizedPatternLog n M f a)| ∂finitePatternRowsLaw (n+1) M)≤
      ∫ _ : Fin M→Fin (n+1)→ℝ,Real.pi*bulkFeatureBound (n+1) v^2 ∂finitePatternRowsLaw (n+1) M :=
      integral_mono (hj.integral_prod_left.sub (normalizedPatternLog_integrable n M f)).abs (integrable_const _) hp
    _=_ := by simp

lemma cavityAveragedLog_unperturbed_bound {α : ℝ} (_hα : 0≤α) (f : ℝ→ᵇℝ) (n : ℕ) :
    |cavityAveragedLog α f n/(n+1:ℕ)-expectedPressure α 1 f (n+1)|≤
      4*Real.pi*bulkScale (n+1)^2/(n+1:ℕ) := by
  let A:=∫ a,normalizedPatternLog n (patternCount α (n+1)) f a ∂finitePatternRowsLaw (n+1) (patternCount α (n+1))
  have he : expectedPressure α 1 f (n+1)=A/(n+1:ℕ) := by
    unfold expectedPressure
    simp_rw [←normalizedPatternLog_source α 1 f n,one_smul]
    rw [integral_const_mul]
    change (1/(n+1:ℕ))*A=A/(n+1:ℕ)
    ring
  have hv : ∀ᵐ v ∂bulkParameterLaw,|bulkExpectedLog n (patternCount α (n+1)) f v-A|≤
      4*Real.pi*bulkScale (n+1)^2 := by
    filter_upwards [bulkParameterLaw_ae] with v hv
    have hb:=bulkFeatureBound_sq_le (n+1) v (by norm_num : (0:ℝ)≤2)
      (fun p=>abs_le.mpr ⟨by linarith [(hv (p+1)).1],(hv (p+1)).2⟩)
    have hi:=bulkExpectedLog_unperturbed_bound n (patternCount α (n+1)) f v
    change |bulkExpectedLog n (patternCount α (n+1)) f v-A|≤_ at hi
    nlinarith [Real.pi_pos]
  have ha : |cavityAveragedLog α f n-A|≤4*Real.pi*bulkScale (n+1)^2 := by
    have hi:=(bulkExpectedLog_parameter_integrable n (patternCount α (n+1)) f).sub (integrable_const A)
    have hh:=integral_mono_ae hi.abs (integrable_const (4*Real.pi*bulkScale (n+1)^2)) hv
    have hh':=abs_integral_le_integral_abs (f:=fun v=>bulkExpectedLog n (patternCount α (n+1)) f v-A) (μ:=bulkParameterLaw)
    simp only [integral_sub (bulkExpectedLog_parameter_integrable _ _ f) (integrable_const A),
      integral_const,probReal_univ,one_smul] at hh hh'
    exact hh'.trans hh
  rw [he,←sub_div,abs_div,abs_of_pos (by positivity : (0:ℝ)<(n+1:ℕ))]
  exact div_le_div_of_nonneg_right ha (by positivity)

lemma bulkScale_per_coordinate_tendsto :
    Tendsto (fun n : ℕ=>4*Real.pi*bulkScale (n+1)^2/(n+1:ℕ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have ht:=(tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp hN
  have he (n : ℕ) : bulkScale (n+1)^2/(n+1:ℕ)=((n+1:ℕ):ℝ)^(-(1:ℝ)/4) := by
    rw [bulkScale_sq_eq_rpow]
    have hs:=Real.rpow_sub (by positivity : (0:ℝ)<(n+1:ℕ)) ((3:ℝ)/4) 1
    norm_num at hs
    simpa only [Nat.cast_add,Nat.cast_one,neg_div] using hs.symm
  convert ht.const_mul (4*Real.pi) using 1
  · funext n
    rw [mul_div_assoc,he]
    simp only [Function.comp_apply,neg_div]
  · simp
end SphericalPerceptronFreeEnergy

end

end OAI
