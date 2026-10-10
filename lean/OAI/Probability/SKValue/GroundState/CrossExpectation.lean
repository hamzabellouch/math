import Mathlib
import OAI.Probability.SKValue.Control.Regularity

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma predictableCenteredSquare_mean {N j : ℕ} (hj : j<N+1)
    {H : (Fin (N+1) → ℝ) → ℝ} (hm : Measurable H) (hp : DependsBefore j H) :
    (∫ z,H z*((coordinate N j z)^2-1) ∂gaussianProduct (Fin (N+1)))=0 := by
  have hind := (hp.independent hj hm).comp measurable_id
    ((measurable_id.pow_const 2).sub (measurable_const (a := (1 : ℝ))))
  have hi := hind.integral_mul_eq_mul_integral hm.aestronglyMeasurable
    (((measurable_coordinate N j).pow_const 2).sub measurable_const).aestronglyMeasurable
  change (∫ z,H z*((coordinate N j z)^2-1) ∂gaussianProduct (Fin (N+1)))=_ at hi
  simp only [Function.comp_apply,Pi.sub_apply,id_eq] at hi
  rw [hi,gaussian_centered_square_mean (coordinate_hasLaw N j),mul_zero]

lemma cross_value_expectation_step {T K L K' L' G t δ : ℝ}
    {γ β : ℝ → ℝ} {V U : ℝ → ℝ → ℝ}
    (hV : ValueStrip T γ V K L) (hU : ValueStrip T β U K' L')
    (ht : 0≤t) (hδ : 0≤δ) (hδ1 : δ≤1) (htδ : t+δ≤T)
    (hG : γ T≤G) (hG' : β T≤G) {N j : ℕ} (hj : j<N+1)
    {Y : (Fin (N+1) → ℝ) → ℝ} (hYm : Measurable Y)
    (hYp : DependsBefore j Y) (hY : MemLp Y 2 (gaussianProduct (Fin (N+1)))) :
    let μ := gaussianProduct (Fin (N+1))
    let Y' := fun z ↦ Y z+Real.sqrt δ*coordinate N j z+δ*(β t*crossFeedback V U t (Y z))
    |((∫ z,U (t+δ) (Y' z)-V (t+δ) (Y' z) ∂μ)-
      (∫ z,U t (Y z)-V t (Y z) ∂μ))+
      (δ/2)*(β t-γ t)*(∫ z,(deriv (V t) (Y z))^2 ∂μ)| ≤
      δ*Real.sqrt δ*(cubicEnvelopeMean G K ((1/2+G)*L)+
        cubicEnvelopeMean G K' ((1/2+G)*L'))+
      δ*K*(γ (t+δ)-γ t)+δ*K'*(β (t+δ)-β t) := by
  let μ := gaussianProduct (Fin (N+1))
  let p := fun z ↦ deriv (V t) (Y z)
  let q := fun z ↦ deriv (U t) (Y z)
  let a := fun z ↦ deriv (deriv (V t)) (Y z)
  let b := fun z ↦ deriv (deriv (U t)) (Y z)
  let Y' := fun z ↦ Y z+Real.sqrt δ*coordinate N j z+δ*(β t*crossFeedback V U t (Y z))
  let P := fun z ↦ Real.sqrt δ*rawIncrement (fun z ↦ q z-p z) j z
  let Q := fun z ↦ (δ/2)*((b z-a z)*((coordinate N j z)^2-1))
  let D := fun z ↦ U (t+δ) (Y' z)-V (t+δ) (Y' z)-(U t (Y z)-V t (Y z))+
    ((δ/2)*(β t-γ t))*(p z)^2
  let R := fun z ↦ D z-P z-Q z
  let E := fun z ↦ δ*Real.sqrt δ*(cubicEnvelope G K ((1/2+G)*L) (coordinate N j z)+
        cubicEnvelope G K' ((1/2+G)*L') (coordinate N j z))+
      δ*K*(γ (t+δ)-γ t)+δ*K'*(β (t+δ)-β t)
  have htT : t≤T := (le_add_of_nonneg_right hδ).trans htδ
  have htm : t∈Icc (0 : ℝ) T := ⟨ht,htT⟩
  have hem : t+δ∈Icc (0 : ℝ) T := ⟨by linarith,htδ⟩
  have hGn : 0≤G := (hV.gamma_nonneg T ⟨ht.trans htT,le_rfl⟩).trans hG
  have hpm : Measurable p := ((hV.smooth t htm).continuous_deriv (by norm_num)).measurable.comp hYm
  have hqm : Measurable q := ((hU.smooth t htm).continuous_deriv (by norm_num)).measurable.comp hYm
  have ham : Measurable a := by
    have hc := (hV.smooth t htm).continuous_iteratedDeriv 2 (by norm_num)
    simp only [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ] at hc
    exact hc.measurable.comp hYm
  have hbm : Measurable b := by
    have hc := (hU.smooth t htm).continuous_iteratedDeriv 2 (by norm_num)
    simp only [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ] at hc
    exact hc.measurable.comp hYm
  have hpM : MemLp p 2 μ := MemLp.of_bound hpm.aestronglyMeasurable 1
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hV.bounded t htm (Y z)))
  have hqM : MemLp q 2 μ := MemLp.of_bound hqm.aestronglyMeasurable 1
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hU.bounded t htm (Y z)))
  have hfp : DependsBefore j (fun z ↦ q z-p z) := by
    intro z z' hz
    dsimp only [p,q]
    rw [hYp z z' hz]
  have hap : DependsBefore j (fun z ↦ b z-a z) := by
    intro z z' hz
    dsimp only [a,b]
    rw [hYp z z' hz]
  have hab (z) : |b z-a z|≤K'+K :=
    (abs_sub _ _).trans (add_le_add (hU.second_bound t htm (Y z)) (hV.second_bound t htm (Y z)))
  have hPi : Integrable P μ :=
    ((rawIncrement_memLp hj (hqm.sub hpm) hfp (hqM.sub hpM)).const_mul _).integrable (by norm_num)
  have hQi : Integrable Q μ :=
    ((predictableCenteredSquare_memLp (hbm.sub ham) hab).const_mul _).integrable (by norm_num)
  have hP0 : (∫ z,P z ∂μ)=0 := by
    dsimp only [P]
    rw [integral_const_mul,rawIncrement_mean (H := fun z ↦ q z-p z) hj (hqm.sub hpm) hfp,mul_zero]
  have hQ0 : (∫ z,Q z ∂μ)=0 := by
    dsimp only [Q]
    rw [integral_const_mul,predictableCenteredSquare_mean (H := fun z ↦ b z-a z) hj (hbm.sub ham) hap,mul_zero]
  have hfM : MemLp (fun z ↦ crossFeedback V U t (Y z)) 2 μ := by
    change MemLp (fun z ↦ (q z+p z)/2) 2 μ
    simpa only [div_eq_mul_inv,Pi.add_apply] using (hqM.add hpM).mul_const ((2 : ℝ)⁻¹)
  have hY'M : MemLp Y' 2 μ :=
    (hY.add ((gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num)).const_mul _)).add
      ((hfM.const_mul (β t)).const_mul δ)
  have hDnext := ((hU.value_memLp hem hY'M).sub (hV.value_memLp hem hY'M)).integrable (by norm_num)
  have hDcur := ((hU.value_memLp htm hY).sub (hV.value_memLp htm hY)).integrable (by norm_num)
  have hDi : Integrable D μ := (hDnext.sub hDcur).add (hpM.integrable_sq.const_mul _)
  have hRi : Integrable R μ := (hDi.sub hPi).sub hQi
  have hE1 := (cubicEnvelope_memLp_two (coordinate_hasLaw N j) hGn K ((1/2+G)*L)).integrable (by norm_num)
  have hE2 := (cubicEnvelope_memLp_two (coordinate_hasLaw N j) hGn K' ((1/2+G)*L')).integrable (by norm_num)
  have hEi : Integrable E μ := (((hE1.add hE2).const_mul _).add (integrable_const _)).add (integrable_const _)
  have hRE (z) : |R z|≤E z := by
    have hh := cross_value_one_step hV hU ht hδ hδ1 htδ hG hG' (x := Y z) (z := coordinate N j z)
    convert hh using 1
    dsimp only [R,D,P,Q,p,q,a,b,Y',E,rawIncrement]
    congr 1
    ring
  have hRmean : (∫ z,R z ∂μ)=(∫ z,D z ∂μ) := by
    dsimp only [R]
    rw [integral_sub (f := fun z ↦ D z-P z) (g := Q) (hDi.sub hPi) hQi,
      integral_sub (f := D) (g := P) hDi hPi,hP0,hQ0,sub_zero,sub_zero]
  have hDmean : (∫ z,D z ∂μ)=
      ((∫ z,U (t+δ) (Y' z)-V (t+δ) (Y' z) ∂μ)-(∫ z,U t (Y z)-V t (Y z) ∂μ))+
      (δ/2)*(β t-γ t)*(∫ z,(p z)^2 ∂μ) := by
    dsimp only [D]
    rw [integral_add (f := fun z ↦ U (t+δ) (Y' z)-V (t+δ) (Y' z)-(U t (Y z)-V t (Y z)))
      (g := fun z ↦ ((δ/2)*(β t-γ t))*(p z)^2) (hDnext.sub hDcur) (hpM.integrable_sq.const_mul _),
      integral_sub (f := fun z ↦ U (t+δ) (Y' z)-V (t+δ) (Y' z))
      (g := fun z ↦ U t (Y z)-V t (Y z)) hDnext hDcur,integral_const_mul]
  have hEmean : (∫ z,E z ∂μ)=
      δ*Real.sqrt δ*(cubicEnvelopeMean G K ((1/2+G)*L)+cubicEnvelopeMean G K' ((1/2+G)*L'))+
      δ*K*(γ (t+δ)-γ t)+δ*K'*(β (t+δ)-β t) := by
    dsimp only [E]
    rw [integral_add (f := fun z ↦ δ*Real.sqrt δ*(cubicEnvelope G K ((1/2+G)*L) (coordinate N j z)+
      cubicEnvelope G K' ((1/2+G)*L') (coordinate N j z))+δ*K*(γ (t+δ)-γ t))
      (g := fun _ ↦ δ*K'*(β (t+δ)-β t))
      (((hE1.add hE2).const_mul _).add (integrable_const _)) (integrable_const _),
      integral_add (f := fun z ↦ δ*Real.sqrt δ*(cubicEnvelope G K ((1/2+G)*L) (coordinate N j z)+
      cubicEnvelope G K' ((1/2+G)*L') (coordinate N j z))) (g := fun _ ↦ δ*K*(γ (t+δ)-γ t))
      ((hE1.add hE2).const_mul _) (integrable_const _),integral_const_mul,
      integral_add (f := fun z ↦ cubicEnvelope G K ((1/2+G)*L) (coordinate N j z))
      (g := fun z ↦ cubicEnvelope G K' ((1/2+G)*L') (coordinate N j z)) hE1 hE2]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    have hm (K L : ℝ) : (∫ z,cubicEnvelope G K L (coordinate N j z) ∂gaussianProduct (Fin (N+1)))=
        cubicEnvelopeMean G K L := by
      simpa only [Function.comp_def,cubicEnvelopeMean,standardGaussian] using
        (coordinate_hasLaw N j).integral_comp (measurable_cubicEnvelope G K L).aestronglyMeasurable
    rw [hm,hm]
  change |((∫ z,U (t+δ) (Y' z)-V (t+δ) (Y' z) ∂μ)-(∫ z,U t (Y z)-V t (Y z) ∂μ))+
    (δ/2)*(β t-γ t)*(∫ z,(p z)^2 ∂μ)|≤_
  rw [←hDmean,←hRmean,←hEmean]
  exact (abs_integral_le_integral_abs).trans (integral_mono hRi.norm hEi hRE)

end SKValue

end

end OAI
