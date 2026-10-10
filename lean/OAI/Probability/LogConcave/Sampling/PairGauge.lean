import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.CircuitParameters
import OAI.Probability.LogConcave.OraclePrograms.MeanSize
import OAI.Probability.LogConcave.OraclePrograms.MeanCorrect
import OAI.Probability.LogConcave.Sampling.AnchorGauge
import OAI.Probability.LogConcave.Numerics.CenterValuesMono

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeanTree MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable {d : ℕ}

def pairGauge (C : ℝ) (z : Point d × Point d) : ℝ := 1+C+‖z‖
lemma pairGauge_measurable (C : ℝ) : Measurable (pairGauge (d:=d) C) := by unfold pairGauge; fun_prop
lemma one_le_pairGauge {C : ℝ} (hC : 0≤C) (z : Point d × Point d) : 1≤pairGauge C z := by
  unfold pairGauge; linarith [norm_nonneg z]
lemma pairGauge_change (C : ℝ) (x y : Point d × Point d) :
    pairGauge C y≤pairGauge C x+dist x y := by
  have hh := norm_le_norm_add_norm_sub x y
  dsimp [pairGauge]
  rw [dist_eq_norm]
  linarith

namespace OracleCompiler.CircuitParameters
variable (C : CircuitParameters)
lemma meanTree_centerValues {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r σ : ℝ} (hr : 0<r) (hσ : 0<σ) (hψ : 0≤C.ψ)
    (hA : C.A=C.actualA) (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1)
    (hsmall : (lam:ℝ)*C.meanCenterBudget r σ*(2*Real.pi+2)≤1)
    (x Y G : Point d) :
    centerValues F (2*(depth (C.meanTree (d:=d) r σ):ℝ)*pairGauge (circuitD F x) (Y,G))
      (C.meanTree r σ) (x,(Y,G)) := by
  have hT : 0≤C.T := by linarith [C.T_lower]
  have hw := (C.meanTree_actual_weights (d:=d) hr hσ hψ).2
  rw [←hA] at hw
  have hg := (literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=C.N) (nc:=C.nc) (Nc:=C.Nc)
    (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint).2
  have hh := centerValues_of_direct hF hr.le hT C.T_upper C.v_nonneg hl hL hsmall
    Prod.fst (fun z : MeanInput d => z.2.1) (fun z : MeanInput d => z.2.2) (x,(Y,G))
    (depth (C.meanTree r σ)) (C.meanTree r σ) hw le_rfl hg
  apply centerValues_mono _ _ _ hh
  have hv : C.v≤1 := by nlinarith [C.angle_small,C.residual_le_one]
  have hY : ‖Y‖≤‖(Y,G)‖ := show ‖Y‖ ≤ max ‖Y‖ ‖G‖ from le_max_left _ _
  have hG : ‖G‖≤‖(Y,G)‖ := show ‖G‖ ≤ max ‖Y‖ ‖G‖ from le_max_right _ _
  have hc := circuitD_nonneg F x
  have hvG := mul_le_of_le_one_left (norm_nonneg G) hv
  have hlr := mul_le_of_le_one_left (show 0≤‖Y‖+C.v*‖G‖ by positivity [C.v_nonneg]) hL
  have he : circuitD F x+(lam:ℝ)*r*(‖Y‖+C.v*‖G‖)≤2*pairGauge (circuitD F x) (Y,G) := by
    change circuitD F x+(lam:ℝ)*r*(‖Y‖+C.v*‖G‖)≤2*(1+circuitD F x+‖(Y,G)‖)
    linarith
  have hmult := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (depth (C.meanTree (d:=d) r σ)): (0:ℝ)≤_)
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hmult

lemma sampleTree_centerValues {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r η : ℝ} (hr : 0<r) (hη : 0<η) (hη1 : η≤1)
    (hA : C.A=C.actualA) (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1)
    (hsmall : (lam:ℝ)*C.sampleCenterBudget r*(2*Real.pi+2)≤1)
    (x Y : Point d) :
    centerValues F ((depth (C.sampleTree (d:=d) r η hη hη1):ℝ)*anchorGauge (circuitD F x) Y)
      (C.sampleTree r η hη hη1) (x,Y) := by
  have hp := sampleCorrelation_properties hη hη1
  have hw := (C.sampleTree_actual_weights (d:=d) hr hη hη1).2
  rw [←hA] at hw
  have hg := (literalSample_geometry (d:=d) (r:=r) (N:=C.N) (Nat.succ_pos C.n)
    (by linarith [hp.1]) hp.2.1 C.h_pos (C.sampleEndpoint η hη hη1)).2
  have hh := centerValues_of_direct hF hr.le (by linarith [hp.1]) hp.2.1 (by norm_num : (0:ℝ)≤0)
    hl hL hsmall Prod.fst Prod.snd (fun _ : SampleInput d => 0) (x,Y)
    (depth (C.sampleTree r η hη hη1)) (C.sampleTree r η hη hη1) hw le_rfl hg
  apply centerValues_mono _ _ _ hh
  have he : circuitD F x+(lam:ℝ)*r*‖Y‖≤anchorGauge (circuitD F x) Y := by
    have hh := mul_le_of_le_one_left (norm_nonneg Y) hL
    unfold anchorGauge; linarith
  simpa using mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (depth (C.sampleTree (d:=d) r η hη hη1)): (0:ℝ)≤_)
end OracleCompiler.CircuitParameters
end LogConcaveSampling

end

end

end OAI
