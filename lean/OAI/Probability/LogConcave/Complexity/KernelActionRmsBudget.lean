import Mathlib
import OAI.Probability.LogConcave.Numerics.KernelActionPicardRms
import OAI.Probability.LogConcave.Sampling.ProbabilityEndpoint

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory RMSIntegral Quadrature
open scoped Classical BigOperators NNReal

lemma kernelActionPicard_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (ψ : ℝ) (n : ℕ) (hn : 0<n) (m N : ℕ) (s e : ProbabilityNode T h n) :
    Continuous (kernelActionPicard F x r T h ψ n m N s e) := by
  change Continuous (fun p => ∑i,(derivativeWeight (angleNodes m) i/ψ) •
    kernelCorrectionPicard F x r T h (ψ*angleNodes m i) n N s e p)
  apply continuous_finsetSum
  intro i _
  have hc : Continuous (fun v : Point d => (derivativeWeight (angleNodes m) i/ψ) • v) := continuous_const_smul _
  exact hc.comp (kernelCorrectionPicard_continuous hF x hr hl hT0 hT1 hh (ψ*angleNodes m i) n hn N s e)

def kernelActionRmsBudget {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam Ap Ah Lp : ℝ≥0) (r R ρ h ψ C J : ℝ) (k n m N : ℕ) : ℝ :=
  2*((∑i,|derivativeWeight (angleNodes m) i/ψ|)*
    (∑i,|derivativeWeight (angleNodes m) i/ψ| *
      kernelValueRmsBudget F x lam Ap Ah Lp r R ρ h (ψ*angleNodes m i) C J k n N))+
  2*(((∑i,|derivativeWeight (angleNodes m) i|)/ψ)^2*
    (((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
      ((d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1))))

theorem kernelActionPicard_terminal_rms (n : ℕ) (hn : 0<n) :
    ∃Ap Ah Lp Lh : ℝ≥0,∃C J : ℝ,0≤C ∧ 1≤J ∧ ∃k : ℕ,
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
      ∀(x : Point d) {r : ℝ},∀hr : 0<r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
      Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀s : ProbabilityNode T h n,
      let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
      ∀R : ℝ,0<R → R^2≤1-T^2 → ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m≤1 →
      let err := fun p : Point d × Point d =>
        kernelActionPicard F x r T h ψ n m N s (probabilityEndpoint hT0 hT1 hh n) p-
          (terminalJacobian hF x hr hl hT0.le hT1 (S,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2
      Integrable (fun p => ‖err p‖^2) ((interpolationLaw F x r T).prod (stdGaussian (Point d))) ∧
      (∫p,‖err p‖^2 ∂((interpolationLaw F x r T).prod (stdGaussian (Point d))))≤
        kernelActionRmsBudget F x lam Ap Ah Lp r R S h ψ C J k n m N := by
  obtain ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,hA⟩ := kernelActionPicard_rms n hn
  refine ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s
  dsimp only
  let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
  let ep := probabilityEndpoint hT0 hT1 hh n
  let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n ep,probabilityNodeTime_mem hT0 hT1 hh hn ep⟩
  have hE : E=⟨T,hT0.le,le_rfl⟩ := Subtype.ext (probabilityEndpoint_time hT0 hT1 hh n hn)
  intro R hR hRT m hm1 ψ hψ hψm
  let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S ⟨T,hT0.le,le_rfl⟩
  let inp := fun y : Point (d+d) => (fw (productPointEquiv d d y).1,(productPointEquiv d d y).2)
  let err := fun p : Point d × Point d => kernelActionPicard F x r T h ψ n m N s ep p-
    (terminalJacobian hF x hr hl hT0.le hT1 (S,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2
  have ha := hA hF x hr hlam hl hd hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s ep R hR hRT m hm1 ψ hψ hψm
  let aerr := fun f : Point d → Point d => fun y : Point (d+d) =>
    kernelActionPicard F x r T h ψ n m N s ep
      (f (productPointEquiv d d y).1,(productPointEquiv d d y).2)-kernelTransportAction f y
  change Integrable (fun y => ‖aerr (probabilityTransport hF x hr.le hl hT0.le hT1 S E) y‖^2)
      (gibbs (centeringPotential F x r S)) ∧
    (∫y,‖aerr (probabilityTransport hF x hr.le hl hT0.le hT1 S E) y‖^2
      ∂gibbs (centeringPotential F x r S))≤kernelActionRmsBudget F x lam Ap Ah Lp r R S h ψ C J k n m N at ha
  rw [hE] at ha
  have heq (y : Point (d+d)) : err (inp y)=kernelActionPicard F x r T h ψ n m N s ep (inp y)-kernelTransportAction fw y := by
    dsimp only [err,inp]
    rw [kernelTransportAction_terminal,terminalForward_eq]
  have hfw : Measurable fw := (probabilityTransport_continuous hF x hr.le hl hT0.le hT1 S ⟨T,hT0.le,le_rfl⟩).measurable
  have hinp : Measurable inp := (hfw.comp ((productPointEquiv d d).continuous.measurable.fst)).prodMk
    ((productPointEquiv d d).continuous.measurable.snd)
  have hlaw := centering_transport_joint_law hF x hr.le hl hT0.le hT1 S ⟨T,hT0.le,le_rfl⟩
  have hK : Continuous (fun p : Point d × Point d =>
      (terminalJacobian hF x hr hl hT0.le hT1 (S,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2) :=
    (((terminalJacobian_smooth hF x hr hl hT0.le hT1).continuous.comp
      (continuous_const.prodMk continuous_fst)).sub continuous_const).clm_apply continuous_snd
  have he : Measurable err := ((kernelActionPicard_continuous hF x hr.le hl hT0 hT1 hh ψ n hn m N s ep).sub hK).measurable
  have hi : Integrable (fun y => ‖err (inp y)‖^2) (gibbs (centeringPotential F x r S)) := by
    simpa only [heq] using ha.1
  have hb : (∫y,‖err (inp y)‖^2 ∂gibbs (centeringPotential F x r S))≤
      kernelActionRmsBudget F x lam Ap Ah Lp r R S h ψ C J k n m N := by
    simpa only [heq] using ha.2
  exact rms_bound_pushforward hinp hlaw he hi hb
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory RMSIntegral Quadrature
open scoped Classical BigOperators NNReal

def kernelQuadraturePicard {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h ψ : ℝ) (n m N : ℕ) (e : ProbabilityNode T h n)
    (w : ProbabilityNode T h n → ℝ) (p : Point d × Point d) : Point d :=
  ∑s,w s • kernelActionPicard F x r T h ψ n m N s e p

theorem kernelQuadraturePicard_numerical_rms (n : ℕ) (hn : 0<n) :
    ∃Ap Ah Lp Lh : ℝ≥0,∃C J : ℝ,0≤C ∧ 1≤J ∧ ∃k : ℕ,
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
      ∀(x : Point d) {r : ℝ},∀hr : 0<r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
      Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀R : ℝ,0<R → R^2≤1-T^2 → ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m≤1 →
      ∀w : ProbabilityNode T h n → ℝ,
      let err := fun p : Point d × Point d =>
        kernelQuadraturePicard F x r T h ψ n m N (probabilityEndpoint hT0 hT1 hh n) w p-
          ∑s,w s • (terminalJacobian hF x hr hl hT0.le hT1
            (probabilityNodeTime T h n s,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2
      Integrable (fun p => ‖err p‖^2) ((interpolationLaw F x r T).prod (stdGaussian (Point d))) ∧
      (∫p,‖err p‖^2 ∂((interpolationLaw F x r T).prod (stdGaussian (Point d))))≤
        (∑s,|w s|)*(∑s,|w s| *
          kernelActionRmsBudget F x lam Ap Ah Lp r R (probabilityNodeTime T h n s) h ψ C J k n m N) := by
  obtain ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,hA⟩ := kernelActionPicard_terminal_rms n hn
  refine ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hqp hqh hqlp hqlh N R hR hRT m hm1 ψ hψ hψm w
  dsimp only
  let ep := probabilityEndpoint hT0 hT1 hh n
  let f := fun (s : ProbabilityNode T h n) (p : Point d × Point d) =>
    kernelActionPicard F x r T h ψ n m N s ep p-
      (terminalJacobian hF x hr hl hT0.le hT1
        (probabilityNodeTime T h n s,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2
  have hs (s : ProbabilityNode T h n) :=
    hA hF x hr hlam hl hd hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s R hR hRT m hm1 ψ hψ hψm
  have hfc (s : ProbabilityNode T h n) : Continuous (f s) := by
    have hK : Continuous (fun p : Point d × Point d =>
        (terminalJacobian hF x hr hl hT0.le hT1
          (probabilityNodeTime T h n s,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2) :=
      (((terminalJacobian_smooth hF x hr hl hT0.le hT1).continuous.comp
        (continuous_const.prodMk continuous_fst)).sub continuous_const).clm_apply continuous_snd
    exact (kernelActionPicard_continuous hF x hr.le hl hT0 hT1 hh ψ n hn m N s ep).sub hK
  have he (p : Point d × Point d) :
      kernelQuadraturePicard F x r T h ψ n m N ep w p-
        ∑s,w s • (terminalJacobian hF x hr hl hT0.le hT1
          (probabilityNodeTime T h n s,p.1)-ContinuousLinearMap.id ℝ (Point d)) p.2=
        ∑s,w s • f s p := by
    simp only [kernelQuadraturePicard,f,smul_sub,Finset.sum_sub_distrib]
  simp_rw [show probabilityEndpoint hT0 hT1 hh n=ep from rfl,he]
  exact weighted_sum_sq_varying w f
    (fun s => kernelActionRmsBudget F x lam Ap Ah Lp r R (probabilityNodeTime T h n s) h ψ C J k n m N)
    (fun s => (hfc s).aestronglyMeasurable) (fun s => (hs s).1) (fun s => (hs s).2)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Quadrature
open scoped Classical BigOperators NNReal

theorem kernelQuadraturePicard_lipschitz (n : ℕ) (hn : 0<n) :
    ∃A B : ℝ≥0,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r T h ψ : ℝ},0≤r →
        (lam:ℝ)*r^2≤1/2 → 0<T → T<1 → 0<h → 0<ψ →
        ∀m : ℕ,ψ*m≤1 →
        A*probabilityMeanLipschitz lam r≤1/2 →
        B*probabilityMeanLipschitz lam r≤1/2 →
        ∀N : ℕ,∀e : ProbabilityNode T h n,∀w : ProbabilityNode T h n → ℝ,
      LipschitzWith ((∑s,‖w s‖₊)*
        ((∑i : Fin (m+1),‖derivativeWeight (angleNodes m) i/ψ‖₊)*
          (16*(A*probabilityMeanLipschitz lam r))))
        (kernelQuadraturePicard F x r T h ψ n m N e w) := by
  obtain ⟨A,B,hAB⟩ := kernelActionPicard_lipschitz n hn
  refine ⟨A,B,?_⟩
  intro d F lam hF x r T h ψ hr hl hT0 hT1 hh hψ m hψm hq hq' N e w
  exact finite_weighted_lipschitz w
    (fun s => kernelActionPicard F x r T h ψ n m N s e)
    (fun s => hAB hF x hr hl hT0 hT1 hh hψ m hψm hq hq' N s e)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.FinitePicard
open MeasureTheory
open scoped BigOperators NNReal RealInnerProductSpace

variable {Ω E I : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]

lemma iterateLp_ae (w : I → I → ℝ) (φ : I → E → E) {K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a : I → Lp E 2 ν) (n : ℕ) :
    ∀ᵐω ∂ν,∀i, ((stepLp w φ hφ a)^[n] a i) ω=
      nodes w φ (fun ω j => a j ω) n ω i := by
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun _ _ => rfl)
  | succ n ih =>
    have hs : ∀ᵐω ∂ν,∀i,
        (stepLp w φ hφ a ((stepLp w φ hφ a)^[n] a) i) ω=
          step w φ (fun j => a j ω) (fun j => (((stepLp w φ hφ a)^[n] a) j) ω) i := by
      rw [ae_all_iff]
      exact stepLp_ae w φ hφ a _
    filter_upwards [hs,ih] with ω hs hi
    intro i
    rw [Function.iterate_succ_apply',hs i]
    simp only [nodes,hi]

theorem actual_nodes_rms (w : I → I → ℝ) (φ : I → E → E) {A K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a e : I → Lp E 2 ν)
    (hw : ∀i,∑j,|w i j|≤A) (hq : (A*K:ℝ≥0)≤1/2)
    {D : ℝ} (hD : 0≤D)
    (he : ∀i,(∫ω,‖(stepLp w φ hφ a e i) ω-e i ω‖^2 ∂ν)≤D^2)
    (n : ℕ) (i : I) :
    (∫ω,‖nodes w φ (fun ω j => a j ω) n ω i-e i ω‖^2 ∂ν)≤
      (2*D+(A*K:ℝ≥0)^n*dist a e)^2 := by
  have hh := rms_picard_defect w φ hφ a e hw hq hD
    (fun i => nodewise_rms_le hD (he i)) n
  have hj := (dist_le_pi_dist ((stepLp w φ hφ a)^[n] a) e i).trans hh
  have hn : 0≤2*D+(A*K:ℝ≥0)^n*dist a e := by positivity
  have heq : (∫ω,‖nodes w φ (fun ω j => a j ω) n ω i-e i ω‖^2 ∂ν)=
      dist (((stepLp w φ hφ a)^[n] a) i) (e i)^2 := by
    rw [dist_eq_norm,lp_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [iterateLp_ae w φ hφ a n,
      Lp.coeFn_sub (((stepLp w φ hφ a)^[n] a) i) (e i)] with ω h1 h2
    simp only [h2,Pi.sub_apply,h1 i]
  rw [heq]
  exact pow_le_pow_left₀ dist_nonneg hj 2
end LogConcaveSampling.FinitePicard

end

end

end

end OAI
