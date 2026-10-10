import Mathlib
import OAI.Geometry.SmoothYau.Estimates.NormalFamilyPhase
import OAI.Geometry.SmoothYau.Geometry.ActualMetricSuperpositionSmallBall

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

def normalPhaseCovector (q : NormalWaveParameter) (z : Fin 3 → ℂ) : NormalWaveSpace →L[ℝ] ℂ :=
  ∑ i : Fin 3, ((ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    (normalWaveEquiv.symm.toContinuousLinearMap.comp q.2.inverse)).smulRight (z i)

lemma normalPhaseCovector_apply (q : NormalWaveParameter) (z : Fin 3 → ℂ) (v : NormalWaveSpace) :
    normalPhaseCovector q z v = ∑ i, ((normalWaveEquiv.symm (q.2.inverse v)) i : ℂ)*z i := by
  simp [normalPhaseCovector,Complex.real_smul]

lemma normal_centered_fderiv_eq_inverse (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K)
    (ψ : NormalWaveSpace → NormalWaveSpace)
    (hder : q.2.comp (fderiv ℝ ψ 0) = ContinuousLinearMap.id ℝ NormalWaveSpace) :
    fderiv ℝ ψ 0 = q.2.inverse := by
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  ext v : 1
  have hd := congrArg (fun L : NormalWaveSpace →L[ℝ] NormalWaveSpace => L v) hder
  change q.2 (fderiv ℝ ψ 0 v) = v at hd
  rw [←hA,ContinuousLinearMap.inverse_equiv]
  apply A.injective
  have hdA : A (fderiv ℝ ψ 0 v) = v := by
    simpa only [←hA, ContinuousLinearEquiv.coe_coe] using hd
  simpa only [ContinuousLinearEquiv.coe_coe, A.apply_symm_apply] using hdA

lemma normalFamilyPhase_centered_fderiv (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ)
    (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ContDiff ℝ ∞ A) {K : Set NormalWaveSpace} {q : NormalWaveParameter}
    (hq : q ∈ metricFrameSet g K)
    (hA0 : ∀ i j, A (q,0) i j = if i = j then 1 else 0)
    (hAd : ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0)
    (ψ : NormalWaveSpace → NormalWaveSpace) (hψ : ContDiff ℝ ∞ ψ) (hψ0 : ψ 0 = 0)
    (hder : q.2.comp (fderiv ℝ ψ 0) = ContinuousLinearMap.id ℝ NormalWaveSpace)
    (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix) (hn : ∑ i, z i*z i = -1)
    {κ C : ℝ} (hQ : PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q)
    (m D : ℕ) :
    fderiv ℝ (fun t => normalFamilyPhase g φ A q z Q m D (normalWaveEquiv.symm (ψ t))) 0 =
      normalPhaseCovector q z := by
  let G := fun i j x => A (q,x) i j
  let S := smoothPhasePolynomial G (normalWaveProfile g φ q 0 : ℂ) z Q ((2*D+3*m+6)+(D+m+1)+1)
  have hG (i j) : ContDiff ℝ ∞ (G i j) :=
    (contDiff_pi.mp (contDiff_pi.mp hA i) j).comp (contDiff_const.prodMk contDiff_id)
  have hs := smoothPhasePolynomial_spec G hG hA0 hAd (normalWaveProfile g φ q 0 : ℂ)
    z Q (phase_vector_ne_zero _ hn) (fun i j => congrFun (congrFun hQ.1 j) i) hn
    (phase_matrix_annihilation Q z hQ.2.1) ((2*D+3*m+6)+(D+m+1)+1) (by omega)
  have hs1 : ∀ i, MvPolynomial.constantCoeff (MvPolynomial.pderiv i S) = z i := hs.2.1
  have hψ' := normal_centered_fderiv_eq_inverse g hq ψ hder
  have hc := (contDiff_realPolyEval S).differentiable (by simp)
  have hd := (hψ.differentiable (by simp) 0).hasFDerivAt
  have hi := normalWaveEquiv.symm.hasFDerivAt.comp 0 hd
  have hh := (hc (normalWaveEquiv.symm (ψ 0))).hasFDerivAt.comp 0 hi
  change fderiv ℝ ((realPolyEval S) ∘ (normalWaveEquiv.symm ∘ ψ)) 0 = _
  rw [hh.fderiv]
  ext v
  simp only [ContinuousLinearMap.comp_apply,normalPhaseCovector_apply,hψ0,map_zero,hψ',
    ContinuousLinearEquiv.coe_coe,fderiv_realPolyEval,realPolyEval_at_zero,hs1]
end



open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

lemma frame_inverse_apply (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K)
    (v : NormalWaveSpace) : q.2 (q.2.inverse v) = v := by
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  rw [←hA,ContinuousLinearMap.inverse_equiv]
  exact A.apply_symm_apply v

lemma normalPhaseCovector_re (q : NormalWaveParameter) (z : Fin 3 → ℂ)
    (v : NormalWaveSpace) :
    (normalPhaseCovector q z v).re = inner ℝ (q.2.inverse v) (phaseRealVector z) := by
  rw [normalPhaseCovector_apply]
  exact real_phase_linear_general z (q.2.inverse v)

lemma normalPhaseCovector_real_error (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K)
    (z : Fin 3 → ℂ) :
    ‖Complex.reCLM.comp (normalPhaseCovector q z)-fderiv ℝ φ q.1‖ ≤
      ‖q.2.inverse‖*‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro v
  have hv : fderiv ℝ φ q.1 v =
      inner ℝ (gradient (normalWaveProfile g φ q) 0) (q.2.inverse v) := by
    rw [normalWaveProfile_gradient_pairing g hφ,frame_inverse_apply g hq]
  change |(normalPhaseCovector q z v).re-fderiv ℝ φ q.1 v| ≤ _
  rw [normalPhaseCovector_re,hv,real_inner_comm (q.2.inverse v) (gradient (normalWaveProfile g φ q) 0),←inner_sub_right]
  calc
    _ ≤ ‖q.2.inverse v‖*‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖q.2.inverse‖*‖v‖)*‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ :=
      mul_le_mul_of_nonneg_right (q.2.inverse.le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

lemma compact_fderiv_displacement_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q ∈ K, ∀ x : E, ‖x-q‖ ≤ 1 →
      ‖fderiv ℝ f x-fderiv ℝ f q‖ ≤ C*‖x-q‖ := by
  let H := fun w : E × E => fderiv ℝ f (w.1+w.2)
  have hH : ContDiff ℝ ∞ H := (hf.fderiv_right (m := ∞) (by simp)).comp
    (contDiff_fst.add contDiff_snd)
  obtain ⟨C,hC,hb⟩ := compact_fiber_jet_bound H hH (hK.prod (isCompact_closedBall 0 1)) 1
  refine ⟨C,hC,?_⟩
  intro q hq x hx
  have hd (v) (hv : v ∈ Metric.closedBall (0 : E) 1) :
      ‖fderiv ℝ (fun t => H (q,t)) v‖ ≤ C := by
    rw [←norm_iteratedFDeriv_one]
    exact hb (q,v) ⟨hq,hv⟩ 1 le_rfl
  have hu : ContDiff ℝ ∞ (fun t => H (q,t)) := hH.comp (contDiff_const.prodMk contDiff_id)
  have hh := (convex_closedBall (0 : E) 1).norm_image_sub_le_of_norm_fderiv_le
    (fun v _ => hu.differentiable (by simp) v) hd (Metric.mem_closedBall_self zero_le_one)
    (show x-q ∈ Metric.closedBall (0 : E) 1 by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)
  simpa only [H,add_zero,add_sub_cancel,sub_zero] using hh

theorem compact_normal_real_slope_error (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ C > 0, ∀ q ∈ metricFrameSet g K, ∀ z : Fin 3 → ℂ,
      ∀ x : NormalWaveSpace, ‖x-q.1‖ ≤ 1 →
      ‖Complex.reCLM.comp (normalPhaseCovector q z)-fderiv ℝ φ x‖ ≤
        C*(‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖+‖x-q.1‖) := by
  obtain ⟨R,hR,hb⟩ := metricFrameSet_inverse_bound g hK
  obtain ⟨D,hD,hd⟩ := compact_fderiv_displacement_bound φ hφ hK
  refine ⟨R+D,by linarith,?_⟩
  intro q hq z x hx
  have h1 := (normalPhaseCovector_real_error g hφ hq z).trans
    (mul_le_mul_of_nonneg_right (hb q hq) (norm_nonneg _))
  have h2 := hd q.1 hq.1 x hx
  rw [norm_sub_rev] at h2
  have htriangle : ‖Complex.reCLM.comp (normalPhaseCovector q z)-fderiv ℝ φ x‖ ≤
      ‖Complex.reCLM.comp (normalPhaseCovector q z)-fderiv ℝ φ q.1‖ +
      ‖fderiv ℝ φ q.1-fderiv ℝ φ x‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le
      (Complex.reCLM.comp (normalPhaseCovector q z)-fderiv ℝ φ q.1)
      (fderiv ℝ φ q.1-fderiv ℝ φ x)
  have h := htriangle.trans (add_le_add h1 h2)
  refine h.trans ?_
  nlinarith [norm_nonneg (phaseRealVector z-gradient (normalWaveProfile g φ q) 0),
    norm_nonneg (x-q.1)]

end YauCounterexamples
end

end OAI
