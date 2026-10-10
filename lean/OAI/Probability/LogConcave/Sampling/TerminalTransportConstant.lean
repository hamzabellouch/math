import Mathlib
import OAI.Probability.LogConcave.Sampling.MeanMaterialL2
import OAI.Probability.LogConcave.Analysis.PoincareVectorVariance

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal

def terminalTransportConstant : ℝ :=
  2*(|gronwallBound 0 (Real.pi^2+1) 1 1|+1)+1

lemma terminalTransportConstant_pos : 0<terminalTransportConstant := by
  unfold terminalTransportConstant
  positivity

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
  (hl : (lam:ℝ)*r^2≤1/2)

include hF hr hl in
lemma probability_affine_residual (z : Point d) {t : ℝ} (ht : t∈Ico (0:ℝ) 1) :
    dist (-r • primitiveField F x r 0)
      (fullProbabilityVelocity F x r t (z-t • (r • primitiveField F x r 0))) ≤
      2*((lam:ℝ)*r^2)*(Real.pi*Real.sqrt d+‖z‖+2*r*‖primitiveField F x r 0‖) := by
  rw [fullProbabilityVelocity_eq F x r ht.1 ht.2]
  unfold probabilityVelocity
  rw [dist_smul₀,Real.norm_eq_abs,abs_neg,abs_of_nonneg hr,dist_comm,dist_eq_norm]
  have hh := conditionalFieldMean_center_zero_bound hF x hr hl ht.1 ht.2
    (z-t • (r • primitiveField F x r 0))
  have hz : ‖z-t • (r • primitiveField F x r 0)‖≤‖z‖+r*‖primitiveField F x r 0‖ := by
    apply (norm_sub_le _ _).trans
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,abs_of_nonneg ht.1]
    exact add_le_add le_rfl (mul_le_of_le_one_left (by positivity) ht.2.le)
  have hn := hh.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl hz) le_rfl) (by positivity : 0≤2*((lam:ℝ)*r)))
  convert mul_le_mul_of_nonneg_left hn hr using 1
  first | rfl | ring

theorem terminal_transport_error (z : Point d) :
    ‖fullProbabilityFlow hF x hr hl 1 z-(z-r • primitiveField F x r z)‖≤
      terminalTransportConstant*((lam:ℝ)*r^2)*
        (Real.pi*Real.sqrt d+‖z‖+2*r*‖primitiveField F x r 0‖) := by
  let c := primitiveField F x r 0
  let D := Real.pi*Real.sqrt d+‖z‖+2*r*‖c‖
  let ε := 2*((lam:ℝ)*r^2)*D
  let B := |gronwallBound 0 (Real.pi^2+1) 1 1|+1
  let f (t : ℝ) := fullProbabilityFlow hF x hr hl t z
  let g (t : ℝ) := z-t • (r • c)
  have hv (t : ℝ) : LipschitzWith ⟨Real.pi^2+1,by positivity⟩ (fullProbabilityVelocity F x r t) := by
    apply (fullProbabilityVelocity_lipschitz hF x hr hl t).weaken
    change (Real.pi^2/2)*(lam:ℝ)*r^2≤Real.pi^2+1
    have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0≤Real.pi^2/2)
    nlinarith [sq_nonneg Real.pi]
  have hf : Continuous f := fullProbabilityFlow_time_continuous hF x hr hl z
  have hfd : ∀t∈Icc (0:ℝ) 1,HasDerivWithinAt f
      (fullProbabilityVelocity F x r t (f t)) (Icc 0 1) t := by
    intro t ht
    exact GlobalODE.flow_deriv (a:=0) (b:=1)
      (fun t _ => fullProbabilityVelocity_lipschitz hF x hr hl t)
      (fullProbabilityVelocity_continuous hF x hr hl) ⟨0,le_rfl,by norm_num⟩ z t ht
  have hgd (t : ℝ) : HasDerivAt g (-r • c) t := by
    convert (hasDerivAt_const t z).sub ((hasDerivAt_id t).smul_const (r • c)) using 1 <;> first | rfl | simp
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hh := dist_le_of_approx_trajectories_ODE hv hf.continuousOn
    (GlobalODE.right_deriv hfd) (εf:=0) (fun t _ => by simp) hg.continuousOn
    (fun t _ => (hgd t).hasDerivWithinAt) (εg:=ε)
    (fun t ht => probability_affine_residual hF x hr hl z ht)
    (δ:=0) (by simp only [f,g,fullProbabilityFlow_initial,Function.id_def,zero_smul,sub_zero,dist_self,le_refl])
    1 ⟨by norm_num,le_rfl⟩
  simp only [zero_add,sub_zero] at hh
  rw [GlobalODE.gronwallBound_zero_linear] at hh
  change dist (f 1) (g 1)≤ε*gronwallBound 0 (Real.pi^2+1) 1 1 at hh
  have he : dist (f 1) (g 1)≤ε*B := hh.trans (mul_le_mul_of_nonneg_left
    (by dsimp [B]; linarith [le_abs_self (gronwallBound 0 (Real.pi^2+1) 1 1)]) (by dsimp [ε,D]; positivity))
  have hc := (primitiveField_lipschitz hF x hr).dist_le_mul z 0
  simp only [dist_eq_norm,sub_zero,NNReal.coe_mul,NNReal.coe_mk] at hc
  have hbase : dist (g 1) (z-r • primitiveField F x r z)≤((lam:ℝ)*r^2)*‖z‖ := by
    simp only [g,one_smul,dist_sub_left,dist_smul₀,Real.norm_eq_abs,abs_of_nonneg hr]
    rw [dist_comm,dist_eq_norm]
    convert mul_le_mul_of_nonneg_left hc hr using 1
    first | rfl | ring
  have hD : ‖z‖≤D := by dsimp [D]; linarith [mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg (d:ℝ)),mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hr) (norm_nonneg c)]
  have htot := (dist_triangle (f 1) (g 1) (z-r • primitiveField F x r z)).trans
    (add_le_add he (hbase.trans (mul_le_mul_of_nonneg_left hD (by positivity))))
  change dist (f 1) (z-r • primitiveField F x r z)≤_
  convert htot using 1
  first | rfl | (dsimp [ε,B,terminalTransportConstant,D,c]; ring)
end LogConcaveSampling

end

end

end

end OAI
