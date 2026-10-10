import OAI.NumberTheory.Jacobsthal.Analysis.TerminalForceIntegral

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary

noncomputable def windowKernel (S a u c : ℝ) : ℝ :=
  ((S+a+u+2*c)^3-(S+2*a)^3)/(12*(max 1 a)*(max 1 u)*(max 1 c)^2)
noncomputable def windowMiddle (S a u : ℝ) : ℝ :=
  ∫ c : ℝ in 1..baseCutoff u,windowKernel S a u c
noncomputable def windowOuter (S a : ℝ) : ℝ :=
  ∫ u : ℝ in 1..baseCutoff a,windowMiddle S a u
noncomputable def windowMass (S b : ℝ) : ℝ :=
  ∫ a : ℝ in 1..baseCutoff b,windowOuter S a

theorem windowKernel_continuous (S : ℝ) :
    Continuous (fun q : (ℝ×ℝ)×ℝ => windowKernel S q.1.1 q.1.2 q.2) := by
  have hn : Continuous (fun q : (ℝ×ℝ)×ℝ => (S+q.1.1+q.1.2+2*q.2)^3-(S+2*q.1.1)^3) := by fun_prop
  have hd : Continuous (fun q : (ℝ×ℝ)×ℝ => 12*(max 1 q.1.1)*(max 1 q.1.2)*(max 1 q.2)^2) := by fun_prop
  apply hn.div hd
  intro q
  have h1 : 0 < max (1:ℝ) q.1.1 := (by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)
  have h2 : 0 < max (1:ℝ) q.1.2 := (by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)
  have h3 : 0 < max (1:ℝ) q.2 := (by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)
  positivity

theorem windowMiddle_continuous (S : ℝ) : Continuous (fun p : ℝ×ℝ => windowMiddle S p.1 p.2) := by
  exact continuous_variable_upper_integral (fun p c => windowKernel S p.1 p.2 c)
    (windowKernel_continuous S) (fun p => baseCutoff p.2)
    (continuous_const.max (continuous_const.min continuous_snd))

theorem windowOuter_continuous (S : ℝ) : Continuous (windowOuter S) := by
  have hp : Continuous (fun q : (ℝ×ℝ)×ℝ => (q.1.1,q.2)) := by fun_prop
  have hF : Continuous (fun q : (ℝ×ℝ)×ℝ => windowMiddle S q.1.1 q.2) :=
    (windowMiddle_continuous S).comp hp
  have hcap : Continuous (fun p : ℝ×ℝ => baseCutoff p.1) :=
    continuous_const.max (continuous_const.min continuous_fst)
  have hh : Continuous (fun p : ℝ×ℝ => ∫ u : ℝ in 1..baseCutoff p.1,windowMiddle S p.1 u) :=
    continuous_variable_upper_integral (fun p u => windowMiddle S p.1 u) hF (fun p => baseCutoff p.1) hcap
  have hmap : Continuous (fun a : ℝ => (a,(0:ℝ))) := by fun_prop
  change Continuous (fun a : ℝ => ∫ u : ℝ in 1..baseCutoff a,windowMiddle S a u)
  simpa only [Function.comp_def] using! hh.comp hmap

theorem windowKernel_literal {S a u c : ℝ} (ha : 1 ≤ a) (hu : 1 ≤ u) (hc : 1 ≤ c) :
    windowKernel S a u c=lastWindowCoefficient S a u c/(a*u*c) := by
  rw [windowKernel,max_eq_right ha,max_eq_right hu,max_eq_right hc,lastWindowCoefficient]
  ring

theorem scalarTailMass_zero_eq_windowMass {S b : ℝ} (hS : 0 ≤ S) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass 0 S b=windowMass S b := by
  rw [scalarTailMass_zero_triple hS hb1 hb2,windowMass,baseCutoff_on hb1 hb2]
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le hb1] at ha
  dsimp only
  rw [windowOuter,baseCutoff_on ha.1 (ha.2.trans hb2)]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ha.1] at hu
  dsimp only
  rw [windowMiddle,baseCutoff_on hu.1 (hu.2.trans (ha.2.trans hb2))]
  apply intervalIntegral.integral_congr
  intro c hc
  rw [uIcc_of_le hu.1] at hc
  exact (windowKernel_literal ha.1 hu.1 hc.1).symm

end ErdosOmissionTail

end

end Erdos970

end OAI
