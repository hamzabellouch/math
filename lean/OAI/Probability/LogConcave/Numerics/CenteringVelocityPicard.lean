import Mathlib
import OAI.Probability.LogConcave.Complexity.KernelActionRmsBudget
import OAI.Probability.LogConcave.Complexity.KernelAnalyticBudget

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature RMSIntegral
open scoped Classical BigOperators NNReal

theorem kernelQuadraturePicard_full_rms (n : ℕ) :
    ∃Ap Ah Lp Lh : ℝ≥0,∃C J D : ℝ,0≤C ∧ 1≤J ∧ 1≤D ∧ ∃k : ℕ,
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
      ∀(x : Point d) {r : ℝ},∀hr : 0<r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 → h≤logMeshLength T →
      Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
      Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀R : ℝ,0<R → R^2≤1-T^2 → ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m≤1 →
      let w := terminalQuadratureWeight T h n
      let err := fun p : Point d × Point d =>
        kernelQuadraturePicard F x r T h ψ (n+1) m N (probabilityEndpoint hT0 hT1 hh (n+1)) w p-
          r • (centeringKernel hF x hr hl hT0.le hT1 p.1).adjoint p.2
      Integrable (fun p => ‖err p‖^2) ((interpolationLaw F x r T).prod (stdGaussian (Point d))) ∧
      (∫p,‖err p‖^2 ∂((interpolationLaw F x r T).prod (stdGaussian (Point d))))≤
        2*((∑s,|w s|)*(∑s,|w s| *
          kernelActionRmsBudget F x lam Ap Ah Lp r R (probabilityNodeTime T h (n+1) s) h ψ C J k (n+1) m N))+
        2*kernelAnalyticBudget n d lam r T h D := by
  obtain ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,hN⟩ := kernelQuadraturePicard_numerical_rms (n+1) (by omega)
  obtain ⟨D,hD,hDu⟩ := exists_basisDerivative_budget (probabilityNodes (n+1))
  refine ⟨Ap,Ah,Lp,Lh,C,J,D,hC,hJ,hD,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hs hL hqp hqh hqlp hqlh N R hR hRT m hm ψ hψ hψm
  dsimp only
  let w := terminalQuadratureWeight T h n
  let ep := probabilityEndpoint hT0 hT1 hh (n+1)
  let f := kernelQuadraturePicard F x r T h ψ (n+1) m N ep w
  let g := fun p : Point d × Point d => ∑s,w s •
    (terminalJacobian hF x hr hl hT0.le hT1 (probabilityNodeTime T h (n+1) s,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2
  let q := fun p : Point d × Point d => r • (centeringKernel hF x hr hl hT0.le hT1 p.1).adjoint p.2
  have hf : Continuous f := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_const_smul (w i)).comp
      (kernelActionPicard_continuous hF x hr.le hl hT0 hT1 hh ψ (n+1) (by omega) m N i ep)
  have hg : Continuous g := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_const_smul (w i)).comp
      ((((terminalJacobian_smooth hF x hr hl hT0.le hT1).continuous.comp
        (continuous_const.prodMk continuous_fst)).sub continuous_const).clm_apply continuous_snd)
  have hq : Continuous q := by
    apply (continuous_const_smul r).comp
    exact ((ContinuousLinearMap.adjoint.continuous.comp
      ((centeringKernel_smooth hF x hr hlam hl hT0.le hT1).continuous.comp continuous_fst)).clm_apply continuous_snd)
  have hn := hN hF x hr hlam hl hd hT0 hT1 hh hs hqp hqh hqlp hqlh N R hR hRT m hm ψ hψ hψm w
  have ha := terminalQuadrature_kernel_rms hF x hr hlam hl hT0 hT1 hd n D hD hDu hh hs hL
  exact add_error_sq (μ:=((interpolationLaw F x r T).prod (stdGaussian (Point d))))
    hf.measurable hg.measurable hq.measurable hn.1 ha.1 hn.2 ha.2
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature RMSIntegral
open scoped Classical BigOperators NNReal

def centeringVelocityPicard {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h ψ s : ℝ) (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (p : Point d × Point d) : Point d × Point d :=
  (-(r*s)⁻¹ • kernelQuadraturePicard F x r T h ψ (n+1) m N e
      (terminalQuadratureWeight T h n) p,
    s⁻¹ • (conditionalFieldMean F x r T p.1-primitiveExpectedField F x r))

lemma velocity_scale_cancel {r s : ℝ} (hr : 0<r) (hs : 0<s) (lam : ℝ≥0) :
    (‖-(r*s)⁻¹‖₊ : ℝ)*(probabilityMeanLipschitz lam r:ℝ)=
      (Real.pi^2/2)*((lam:ℝ)*r/s) := by
  change |-(r*s)⁻¹| *((Real.pi^2/2)*(lam:ℝ)*r^2)=_
  simp only [abs_neg,abs_inv,abs_mul,abs_of_pos hr,abs_of_pos hs]
  field_simp

theorem centeringVelocityPicard_lipschitz (n : ℕ) :
    ∃A B : ℝ≥0,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r T h ψ s : ℝ},∀hr : 0<r,
        (lam:ℝ)*r^2≤1/2 → ∀hT0 : 0<T,T<1 → 0<h → 0<ψ → 0<s →
        ∀m : ℕ,ψ*m≤1 →
        A*probabilityMeanLipschitz lam r≤1/2 →
        B*probabilityMeanLipschitz lam r≤1/2 →
        ∀N : ℕ,∀e : ProbabilityNode T h (n+1),
      LipschitzWith
        (‖-(r*s)⁻¹‖₊*((∑i,‖terminalQuadratureWeight T h n i‖₊)*
          ((∑i : Fin (m+1),‖derivativeWeight (angleNodes m) i/ψ‖₊)*
            (16*(A*probabilityMeanLipschitz lam r))))+
          ‖s⁻¹‖₊*⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩)
        (centeringVelocityPicard F x r T h ψ s n m N e) := by
  obtain ⟨A,B,hAB⟩ := kernelQuadraturePicard_lipschitz (n+1) (by omega)
  refine ⟨A,B,?_⟩
  intro d F lam hF x r T h ψ s hr hl hT0 hT1 hh hψ hs m hψm hq hq' N e
  have hfirst := (lipschitzWith_smul (-(r*s)⁻¹)).comp
    (hAB hF x hr.le hl hT0 hT1 hh hψ m hψm hq hq' N e (terminalQuadratureWeight T h n))
  have hmean : LipschitzWith ⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩
      (fun y => conditionalFieldMean F x r T y-primitiveExpectedField F x r) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_sub_right] using
      (conditionalFieldMean_lipschitz hF x hr.le hl hT0.le hT1).dist_le_mul y z
  have hf : LipschitzWith 1 (Prod.fst : Point d × Point d → Point d) := LipschitzWith.prod_fst
  have hsecond : LipschitzWith (‖s⁻¹‖₊*⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩)
      (fun p : Point d × Point d => s⁻¹ •
        (conditionalFieldMean F x r T p.1-primitiveExpectedField F x r)) := by
    convert! (lipschitzWith_smul s⁻¹).comp (hmean.comp hf) using 1
    apply Subtype.ext
    change ‖s⁻¹‖*((Real.pi^2/2)*T*((lam:ℝ)*r))=
      ‖s⁻¹‖*(((Real.pi^2/2)*T*((lam:ℝ)*r))*1)
    ring
  exact (hfirst.prodMk hsecond).weaken
    (max_le (le_add_of_nonneg_right (by positivity))
      (le_add_of_nonneg_left (by positivity)))

lemma centeringVelocityPicard_lipschitz_coefficient {r s T h ψ : ℝ}
    (hr : 0<r) (hs : 0<s) (hψ : 0<ψ) (hT0 : 0<T) (hT1 : T<1)
    (lam A : ℝ≥0) (n m : ℕ) :
    ((‖-(r*s)⁻¹‖₊*((∑i,‖terminalQuadratureWeight T h n i‖₊)*
          ((∑i : Fin (m+1),‖derivativeWeight (angleNodes m) i/ψ‖₊)*
            (16*(A*probabilityMeanLipschitz lam r))))+
          ‖s⁻¹‖₊*⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩ : ℝ≥0):ℝ)≤
      (Real.pi^2/2)*((lam:ℝ)*r/s)*
        (16*A*(∑i,|terminalQuadratureWeight T h n i|)*
          ((∑i : Fin (m+1),|derivativeWeight (angleNodes m) i|)/ψ)+1) := by
  have hc := velocity_scale_cancel hr hs lam
  simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_sum]
  change _ + (‖s⁻¹‖*(Real.pi^2/2*T*((lam:ℝ)*r)))≤_
  simp only [coe_nnnorm,Real.norm_eq_abs,abs_div,abs_of_pos hψ,abs_inv,abs_of_pos hs,
    ←Finset.sum_div] at *
  have he : s⁻¹*((Real.pi^2/2)*T*((lam:ℝ)*r))≤
      (Real.pi^2/2)*((lam:ℝ)*r/s) := by
    have hh := mul_le_mul_of_nonneg_right hT1.le
      (show 0≤(Real.pi^2/2)*((lam:ℝ)*r/s) by positivity)
    convert! hh using 1 <;> ring
  calc
    _ = (16*A*(∑i,|terminalQuadratureWeight T h n i|)*
        ((∑i : Fin (m+1),|derivativeWeight (angleNodes m) i|)/ψ))*
          (‖-(r*s)⁻¹‖*(probabilityMeanLipschitz lam r:ℝ))+
        s⁻¹*((Real.pi^2/2)*T*((lam:ℝ)*r)) := by
      simp only [Real.norm_eq_abs]; ring
    _ ≤ (16*A*(∑i,|terminalQuadratureWeight T h n i|)*
        ((∑i : Fin (m+1),|derivativeWeight (angleNodes m) i|)/ψ))*
          ((Real.pi^2/2)*((lam:ℝ)*r/s))+
        (Real.pi^2/2)*((lam:ℝ)*r/s) := by rw [show ‖-(r*s)⁻¹‖*(probabilityMeanLipschitz lam r:ℝ)=(Real.pi^2/2)*((lam:ℝ)*r/s) from hc]; exact add_le_add le_rfl he
    _ = _ := by ring
end LogConcaveSampling

end

end

end OAI
