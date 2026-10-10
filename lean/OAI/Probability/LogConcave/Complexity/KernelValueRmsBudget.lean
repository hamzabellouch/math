import Mathlib
import OAI.Probability.LogConcave.Sampling.KernelTransportAction
import OAI.Probability.LogConcave.Numerics.KernelCorrectionPicard

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory RMSIntegral Quadrature
open scoped Classical BigOperators NNReal

def kernelValueRmsBudget {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam Ap Ah Lp : ℝ≥0) (r R ρ h z C J : ℝ) (k n N : ℕ) : ℝ :=
  2*(2*(Lp*probabilityMeanLipschitz lam r):ℝ≥0)^2*
    (32*(probabilityRmsBudget F x lam Ap r h C k n N)^2+
      2*(harmonicRmsBudget F x lam Ah r R ρ z J n N)^2)+
    2*(probabilityRmsBudget F x lam Ap r h C k n (N+1))^2

theorem kernelActionPicard_numerical_rms (n : ℕ) (hn : 0<n) :
    ∃Ap Ah Lp Lh : ℝ≥0,∃C J : ℝ,0≤C ∧ 1≤J ∧ ∃k : ℕ,
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
      ∀(x : Point d) {r : ℝ},∀hr : 0<r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
      Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀s e : ProbabilityNode T h n,
      let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
      let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
      let μ := gibbs (centeringPotential F x r S)
      let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
      ∀R : ℝ,0<R → R^2≤1-(S:ℝ)^2 →
      ∀Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y,Continuous (Ξ y)) → (∀y,Ξ y 0=y) →
      (∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (centeringPotential F x r S) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v) →
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) →
      (∀v∈Icc (0:ℝ) 1,μ.map (fun y => Ξ y v)=μ) →
      ∀m : ℕ,∀ψ : ℝ,0<ψ → ψ*m≤1 →
      let w := fun z y => (productPointEquiv d d (Ξ y z)).1
      let err := fun y => kernelActionPicard F x r T h ψ n m N s e
        (fw (productPointEquiv d d y).1,(productPointEquiv d d y).2)-
          derivativeStencil (angleNodes m) ψ (fun i => fw (w (ψ*angleNodes m i) y)-w (ψ*angleNodes m i) y)
      Integrable (fun y => ‖err y‖^2) μ ∧
      (∫y,‖err y‖^2 ∂μ)≤
        (∑i,|derivativeWeight (angleNodes m) i/ψ|)*
          (∑i,|derivativeWeight (angleNodes m) i/ψ| *
            kernelValueRmsBudget F x lam Ap Ah Lp r R S h (ψ*angleNodes m i) C J k n N) := by
  obtain ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,hV⟩ := kernelCorrectionPicard_rms n hn
  refine ⟨Ap,Ah,Lp,Lh,C,J,hC,hJ,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s e
  dsimp only
  let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
  let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
  let μ := gibbs (centeringPotential F x r S)
  let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
  intro R hR hRT Ξ hc hinit hder hm hlaw m ψ hψ hψm
  let pos := fun y : Point (d+d) => (productPointEquiv d d y).1
  let mom := fun y : Point (d+d) => (productPointEquiv d d y).2
  let w := fun z y => pos (Ξ y z)
  let inp := fun y => (fw (pos y),mom y)
  let v := fun i y => kernelCorrectionPicard F x r T h (ψ*angleNodes m i) n N s e (inp y)-
    (fw (w (ψ*angleNodes m i) y)-w (ψ*angleNodes m i) y)
  have hz (i : Fin (m+1)) : 0≤ψ*angleNodes m i ∧ ψ*angleNodes m i≤1 := by
    refine ⟨mul_nonneg hψ.le (Nat.cast_nonneg _),le_trans ?_ hψm⟩
    apply mul_le_mul_of_nonneg_left _ hψ.le
    change (i:ℝ)≤(m:ℝ)
    exact_mod_cast Nat.le_of_lt_succ i.2
  have hval (i : Fin (m+1)) : Integrable (fun y => ‖v i y‖^2) μ ∧
      (∫y,‖v i y‖^2 ∂μ)≤kernelValueRmsBudget F x lam Ap Ah Lp r R S h (ψ*angleNodes m i) C J k n N :=
    hV hF x hr hlam hl hd hT0 hT1 hh hsmall hqp hqh hqlp hqlh N s e
      R hR hRT Ξ hc hinit hder hm hlaw _ (hz i).1 (hz i).2
  have hpos : Measurable pos := (productPointEquiv d d).continuous.measurable.fst
  have hmom : Measurable mom := (productPointEquiv d d).continuous.measurable.snd
  have hfw : Measurable fw := (probabilityTransport_continuous hF x hr.le hl hT0.le hT1 S E).measurable
  have hinp : Measurable inp := (hfw.comp hpos).prodMk hmom
  have hw (z : ℝ) : Measurable (w z) := hpos.comp (hm.comp (measurable_const.prodMk measurable_id))
  have hv (i : Fin (m+1)) : Measurable (v i) :=
    ((kernelCorrectionPicard_continuous hF x hr.le hl hT0 hT1 hh _ n hn N s e).measurable.comp hinp).sub
      ((hfw.comp (hw _)).sub (hw _))
  have he (y : Point (d+d)) : kernelActionPicard F x r T h ψ n m N s e (inp y)-
      derivativeStencil (angleNodes m) ψ (fun i => fw (w (ψ*angleNodes m i) y)-w (ψ*angleNodes m i) y)=
        ∑i,(derivativeWeight (angleNodes m) i/ψ) • v i y := by
    simp only [kernelActionPicard,derivativeStencil,←Finset.sum_sub_distrib,←smul_sub]
    rfl
  have hh := weighted_sum_sq_varying (fun i => derivativeWeight (angleNodes m) i/ψ) v _
    (fun i => (hv i).aestronglyMeasurable) (fun i => (hval i).1) (fun i => (hval i).2)
  simpa only [←he] using hh
end LogConcaveSampling

end

end

end

end OAI
