import Mathlib
import OAI.Analysis.Conductivity.Branching.CrossingBlock

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma cascadeProfile_crossing_current_deriv {L K s : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hs : K+2 < s) :
    deriv (cascadeProfile L K) s = connectorProfile K (K+2)*exp (-3*L)*
      deriv (crossingFirst L) (s-(K+2+L)) := by
  have he : cascadeProfile L K =ᶠ[𝓝 s]
      fun r => connectorProfile K (K+2)*exp (-3*L)*crossingFirst L (r-(K+2+L)) := by
    filter_upwards [Ioi_mem_nhds hs] with r hr
    exact cascadeProfile_crossing_current hL hK hr.le
  have hd : HasDerivAt (fun r => connectorProfile K (K+2)*exp (-3*L)*crossingFirst L (r-(K+2+L)))
      (connectorProfile K (K+2)*exp (-3*L)*deriv (crossingFirst L) (s-(K+2+L))) s := by
    simpa only [id_eq,mul_one,Function.comp_def] using (((crossingFirst_smooth L).differentiable (by simp) _).hasDerivAt.comp s
      ((hasDerivAt_id s).sub_const (K+2+L))).const_mul (connectorProfile K (K+2)*exp (-3*L))
  rw [he.deriv_eq,hd.deriv]

lemma cascadeProfile_crossing_next_deriv {L K s : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hs : s < cascadeLength L K) :
    cascadeRatio L K*deriv (cascadeProfile L K) (2*(s-cascadeLength L K)) =
      (connectorProfile K (K+2)*exp (-3*L)/2)*deriv (crossingSecond L) (s-(K+2+L)) := by
  have he : (fun r => cascadeRatio L K*cascadeProfile L K (2*(r-cascadeLength L K))) =ᶠ[𝓝 s]
      fun r => connectorProfile K (K+2)*exp (-3*L)*crossingSecond L (r-(K+2+L)) := by
    filter_upwards [Iio_mem_nhds hs] with r hr
    exact cascadeProfile_crossing_next hL hK hr.le
  have hd₁ : HasDerivAt (fun r => cascadeRatio L K*cascadeProfile L K (2*(r-cascadeLength L K)))
      (2*cascadeRatio L K*deriv (cascadeProfile L K) (2*(s-cascadeLength L K))) s := by
    simpa only [id_eq,mul_one,one_mul,Function.comp_def,mul_assoc,mul_left_comm,mul_comm] using (((cascadeProfile_smooth L K).differentiable (by simp) _).hasDerivAt.comp s
      (((hasDerivAt_id s).sub_const (cascadeLength L K)).const_mul 2)).const_mul (cascadeRatio L K)
  have hd₂ : HasDerivAt (fun r => connectorProfile K (K+2)*exp (-3*L)*crossingSecond L (r-(K+2+L)))
      (connectorProfile K (K+2)*exp (-3*L)*deriv (crossingSecond L) (s-(K+2+L))) s := by
    simpa only [id_eq,mul_one,Function.comp_def] using (((crossingSecond_smooth L).differentiable (by simp) _).hasDerivAt.comp s
      ((hasDerivAt_id s).sub_const (K+2+L))).const_mul (connectorProfile K (K+2)*exp (-3*L))
  have hh := he.deriv_eq
  rw [hd₁.deriv,hd₂.deriv] at hh
  linarith

end ScalarConductivity

end

end OAI
