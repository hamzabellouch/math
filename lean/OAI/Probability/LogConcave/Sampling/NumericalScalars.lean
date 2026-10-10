import Mathlib
import OAI.Probability.LogConcave.Sampling.Correlation
import OAI.Probability.LogConcave.Complexity.EventuallySequences

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Quadrature
open scoped Classical NNReal

structure NumericalScalars where
  lam : ℝ≥0
  r : ℝ
  s : ℝ

def NumericalScalars.small (v : NumericalScalars) (bound : ℝ) : Prop :=
  0<v.r ∧ 0<v.s ∧ (v.lam:ℝ)*v.r^2≤bound ∧ (v.lam:ℝ)*v.r/v.s≤bound

def centeringCalibrationGood (d k n N : ℕ) (A Ap Ah Lp contraction : ℝ≥0)
    (C J₀ D κ J t w : ℝ) (v : NumericalScalars) : Prop :=
  let R := (d:ℝ)^(-(κ*t))
  let T := sourceCorrelation (κ*t) d
  let h := (d:ℝ)^(-(κ*w))
  let ψ := (d:ℝ)^(-(κ*(4*t)))
  let E := velocityNormalizedBudget d k n n N v.lam Ap Ah Lp v.r R T h ψ C J₀ D
  let q := centeringRowBudget n*velocityJointLip n n A v.lam v.r T h ψ v.s
  let Z := centerStateEnvelope n N ((v.lam:ℝ)*v.r/v.s) R (q:ℝ) E
  (v.lam:ℝ)*v.r^2≤1/2 ∧ contraction*probabilityMeanLipschitz v.lam v.r≤1/2 ∧
    q≤1/2 ∧ Z≤(d:ℝ)^(-(2*κ*J)) ∧
    centerMeanEnvelope n ((v.lam:ℝ)*v.r/v.s) R Z≤(d:ℝ)^(-(2*κ*J))

theorem centeringScalarCalibration_uniform (k n N ksize : ℕ)
    (A Ap Ah Lp contraction : ℝ≥0) (C J₀ D : ℝ) {S κ J b t w : ℝ}
    (hS : 0≤S) (hκ : 0<κ) (hJ : 1≤J) (hb : 1/2≤b) (ht : 0<t) (htsmall : t<1/100)
    (hw : 0<w) (hwt : w<t)
    (hnw : J+10<w*((n:ℝ)-3)) (hnt : J+10<t*((n:ℝ)-3))
    (hnn : 4*(J+10)<(n:ℝ)) (hN : 10*(J+2)≤(N:ℝ)) :
    ∀ᶠ d : ℕ in atTop,∀v : NumericalScalars,
      v.small (S*dimensionLog d^ksize*(d:ℝ)^(-(κ*b))) →
      centeringCalibrationGood d k n N A Ap Ah Lp contraction C J₀ D κ J t w v := by
  let : Nonempty NumericalScalars := ⟨⟨0,1,1⟩⟩
  apply eventually_forall_of_sequences
  · exact Eventually.of_forall (fun d => ⟨⟨0,1,1⟩,by
      refine ⟨by norm_num,by norm_num,?_,?_⟩ <;>
      simp only [NNReal.coe_zero,zero_mul,zero_div] <;>
      positivity [dimensionLog_nonneg d]⟩)
  · intro f hf
    have hl : LogPowerRate (fun d => ((f d).lam:ℝ)*(f d).r^2) (κ*b) :=
      logPowerRate_of_envelope (Eventually.of_forall (fun d => by positivity))
        (hf.mono (fun _ h => h.2.2.1))
    have hα : LogPowerRate (fun d => ((f d).lam:ℝ)*(f d).r/(f d).s) (κ*b) := by
      apply logPowerRate_of_envelope
      · exact hf.mono (fun _ h => by positivity [h.1,h.2.1])
      · exact hf.mono (fun _ h => h.2.2.2)
    exact centeringScalarCalibration k n N A Ap Ah Lp contraction C J₀ D hκ hJ hb ht htsmall
      hw hwt hnw hnt hnn hN hl hα (hf.mono (fun _ h => h.1)) (hf.mono (fun _ h => h.2.1))
end LogConcaveSampling

end

end

end OAI
