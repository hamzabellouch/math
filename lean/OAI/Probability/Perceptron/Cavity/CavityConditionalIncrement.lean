import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityCompensator
import OAI.Probability.Perceptron.Cavity.CavityFiniteEvaluation
import OAI.Probability.Perceptron.Cavity.CavityTrueShellLower

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cavityOldIncrement (n L M : ℕ) (f : Jet3) (a : Fin M→Fin (n+1)→ℝ)
    (W : NormalizedSpin (n+1)→ℝ) (y : Fin M→Spin L) (p : CavityShellSpin n L) : ℝ :=
  cavityShellPatternEnergy n L M f.f (cavityJoinedPatterns (n+1) L M a y) p-
    normalizedPatternEnergy (n+1) M f.f a p.1+W p.1

lemma cavityOldIncrement_measurable (n L M : ℕ) (f : Jet3) (a : Fin M→Fin (n+1)→ℝ)
    (W : NormalizedSpin (n+1)→ℝ) (hW : Measurable W) :
    Measurable (fun p : CavityShellSpin n L×(Fin M→Spin L)=>cavityOldIncrement n L M f a W p.2 p.1) := by
  have hj : Measurable (fun p : CavityShellSpin n L×(Fin M→Spin L)=>
      cavityJoinedPatterns (n+1) L M a p.2) := by
    unfold cavityJoinedPatterns
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j
    · simpa only [Fin.addCases_left] using (measurable_const : Measurable (fun _ : CavityShellSpin n L×(Fin M→Spin L)=>a i j))
    · simp only [Fin.addCases_right]
      fun_prop
  have he := (normalizedPatternEnergy_continuous (n+1+L) M f.f).measurable.comp
    (hj.prodMk ((cavityShellSpinEmbedding_measurable n L).comp measurable_fst))
  have hb : Measurable (fun p : CavityShellSpin n L×(Fin M→Spin L)=>
      normalizedPatternEnergy (n+1) M f.f a p.1.1) := (normalizedPatternEnergy_continuous (n+1) M f.f).measurable.comp
    (f:=fun p : CavityShellSpin n L×(Fin M→Spin L)=>(a,p.1.1))
    (measurable_const.prodMk measurable_fst.fst)
  exact (he.sub hb).add (hW.comp measurable_fst.fst)

lemma cavityOldIncrement_bound (n L M : ℕ) (f : Jet3) (a : Fin M→Fin (n+1)→ℝ)
    (W : NormalizedSpin (n+1)→ℝ) {E : ℝ} (hW : ∀ x,|W x|≤E)
    (y : Fin M→Spin L) (p : CavityShellSpin n L) :
    |cavityOldIncrement n L M f a W y p|≤2*M*‖f.f‖+E := by
  apply (abs_add_le _ _).trans
  apply (add_le_add ((abs_sub _ _).trans (add_le_add
    (cavityShellPatternEnergy_bound n L M f.f _ p)
    (normalizedPatternEnergy_bound (n+1) M f.f a p.1))) (hW p.1)).trans_eq
  ring

theorem cavity_conditional_old_increment_lower (n k M : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*((k+1)+1)≤n+1)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (μ : Measure (NormalizedSpin (n+1))) [IsProbabilityMeasure μ]
    (a : Fin M→Fin (n+1)→ℝ) (W : NormalizedSpin (n+1)→ℝ)
    (hW : Measurable W) {E : ℝ} (hE : 0≤E) (hWE : ∀ x,|W x|≤E) :
    let K : ℝ:=M/(n+1:ℕ)*‖f.dilationMark h1‖
    let A : NormalizedSpin (n+1)→Fin M→ℝ:=fun x i=>f.d1 (∑ j,a i j*x.val j)
    (∫ y : Fin M→Spin (k+1),Real.log (∫ p,Real.exp (cavityOldIncrement n (k+1) M f a W y p)
      ∂μ.prod (cavityShellProbability n (k+1))) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))≥
    (∫ y : Fin M→Spin (k+1),Real.log (∫ x,Real.exp (W x+(k+1:ℕ)*bulkC (n+1) M f a x/2)*
      sphericalExp k (cavityVectorField M (k+1) (A x) (Real.sqrt (n+1:ℕ))⁻¹ y)
        (Real.sqrt (k+1:ℕ)) ∂μ) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))-K/2-
      Real.exp (2*(E+((k+1:ℕ)+1)*K/2)+(Real.sqrt (n+1:ℕ))⁻¹^2*((k+1:ℕ)+1)^2*M*‖f.d1‖^2)*
        Real.sqrt ((1/(2*(n+1:ℕ)))^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*‖f.d2‖^2)-
      (∫ y : Fin M→Spin (k+1),∑ i,cavityRemainderMajorant
        (cavityRemainderCoefficients f h1 h2 h3 (k+1) ((k+1)+1)) (n+1:ℕ) ‖y i‖
        ∂Measure.pi (fun _=>stdGaussian (Spin (k+1)))) := by
  dsimp only
  have := cavityShellProbability_probability n (k+1) hp
  let A : NormalizedSpin (n+1)→Fin M→ℝ:=fun x i=>f.d1 (∑ j,a i j*x.val j)
  let B : NormalizedSpin (n+1)→Fin M→ℝ:=fun x i=>f.d2 (∑ j,a i j*x.val j)
  let C : NormalizedSpin (n+1)→ℝ:=fun x=>bulkC (n+1) M f a x
  let K : ℝ:=M/(n+1:ℕ)*‖f.dilationMark h1‖
  have hK : 0≤K := by dsimp [K]; positivity
  have hA : Measurable A := by have hm:=f.d1.continuous.measurable; unfold A; fun_prop
  have hB : Measurable B := by have hm:=f.d2.continuous.measurable; unfold B; fun_prop
  have hC : Measurable C := (bulkC_measurable n M f).comp
    (f:=fun x : NormalizedSpin (n+1)=>((a,0),x)) (measurable_const.prodMk measurable_id)
  have hAB (x) (i) : |A x i|≤‖f.d1‖ := f.d1.norm_coe_le_norm _
  have hBB (x) (i) : |B x i|≤‖f.d2‖ := f.d2.norm_coe_le_norm _
  have hCK (x) : |C x|≤K := bulkC_bound n M f h1 (a,0) x
  let U : CavityShellSpin n (k+1)→ℝ:=fun p=>W p.1+‖p.2.val‖^2*C p.1/2
  let V : (Fin M→Spin (k+1))→CavityShellSpin n (k+1)→ℝ:=fun y p=>U p+
    cavityLinearField M (k+1) (A p.1) (Real.sqrt (n+1:ℕ))⁻¹ p.2.val y+
    cavityQuadraticField M (k+1) (B p.1) (1/(2*(n+1:ℕ))) p.2.val y
  have hU : Measurable U := by
    have hw : Measurable (fun p : CavityShellSpin n (k+1)=>W p.1) := hW.comp measurable_fst
    have hc : Measurable (fun p : CavityShellSpin n (k+1)=>C p.1) := hC.comp measurable_fst
    unfold U
    fun_prop
  have hUB (p) : |U p|≤E+((k+1:ℕ)+1)*K/2 :=
    cavity_shell_compensator_bound k _ _ _ _ hK (hCK p.1) (hWE p.1) p.2
  have hVi : Integrable (fun y=>Real.log (∫ p,Real.exp (V y p)
      ∂μ.prod (cavityShellProbability n (k+1)))) (Measure.pi (fun _=>stdGaussian (Spin (k+1)))) :=
    cavity_quadratic_log_integrable (μ.prod (cavityShellProbability n (k+1))) M (k+1)
      (fun p=>A p.1) (fun p=>B p.1) (fun p=>p.2.val) U
      (hA.comp measurable_fst) (hB.comp measurable_fst) measurable_snd.subtype_val hU _ _
      (norm_nonneg _) (norm_nonneg _) (by positivity) (by positivity)
      (fun p=>hAB p.1) (fun p=>hBB p.1) (fun p=>cavity_shell_norm_bound (k+1) p.2) hUB
  have hFi := cavity_log_integrable_of_bound (μ.prod (cavityShellProbability n (k+1)))
    (Measure.pi (fun _ : Fin M=>stdGaussian (Spin (k+1))))
    (fun p=>cavityOldIncrement n (k+1) M f a W p.2 p.1)
    (cavityOldIncrement_measurable n (k+1) M f a W hW)
    (fun _=>2*M*‖f.f‖+E) (integrable_const _) (fun _=>by positivity)
    (fun p y=>cavityOldIncrement_bound n (k+1) M f a W hWE y p)
  let R : (Fin M→Spin (k+1))→ℝ:=fun y=>∑ i,cavityRemainderMajorant
    (cavityRemainderCoefficients f h1 h2 h3 (k+1) ((k+1)+1)) (n+1:ℕ) ‖y i‖
  have hRi : Integrable R (Measure.pi (fun _=>stdGaussian (Spin (k+1)))) := by
    apply integrable_finsetSum
    intro i _
    exact ((measurePreserving_eval (fun _ : Fin M=>stdGaussian (Spin (k+1))) i).integrable_comp
      (cavityRemainderMajorant_integrable _ _ _).aestronglyMeasurable).mpr
        (cavityRemainderMajorant_integrable _ _ _)
  have hpoint (y : Fin M→Spin (k+1)) : Real.log (∫ p,Real.exp (V y p)
      ∂μ.prod (cavityShellProbability n (k+1)))-R y≤
      Real.log (∫ p,Real.exp (cavityOldIncrement n (k+1) M f a W y p)
        ∂μ.prod (cavityShellProbability n (k+1))) := by
    have hv : Measurable (V y) := by
      dsimp [V]
      unfold cavityLinearField cavityQuadraticField
      fun_prop
    have herr (p : CavityShellSpin n (k+1)) :
        |cavityOldIncrement n (k+1) M f a W y p-V y p|≤R y := by
      have hh:=cavity_true_shell_expansion n (k+1) M f h1 h2 h3 hn a y p
      convert hh using 1 <;> try dsimp [cavityOldIncrement,V,U,A,B,C,cavityShellTaylorModel]
      · congr 1
        ring
      · simp only [R,Nat.cast_add,Nat.cast_one]
    have hh:=cavity_log_uniform_change (μ.prod (cavityShellProbability n (k+1)))
      ((cavityOldIncrement_measurable n (k+1) M f a W hW).comp
        (measurable_id.prodMk measurable_const)) hv (A:=2*M*‖f.f‖+E) (by positivity)
      (cavityOldIncrement_bound n (k+1) M f a W hWE y) herr
    simp only [Function.comp_def,id_eq] at hh
    linarith [(abs_le.mp hh).1]
  have hi := integral_mono (hVi.sub hRi) hFi hpoint
  simp only [Pi.sub_apply] at hi
  rw [integral_sub hVi hRi] at hi
  have hs := cavity_expected_shell_lower μ n k M hp A B W C hA hB hW hC
    (Real.sqrt (n+1:ℕ))⁻¹ (1/(2*(n+1:ℕ))) (norm_nonneg _) (norm_nonneg _) hE hK hAB hBB hWE hCK
  exact (sub_le_sub_right hs _).trans hi

end SphericalPerceptronFreeEnergy
end

end OAI
