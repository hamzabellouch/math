import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.CircuitParameters
import OAI.Probability.LogConcave.OraclePrograms.MeanSize
import OAI.Probability.LogConcave.Numerics.BaseVariationCenters

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree MeasureTheory Quadrature Expression
open scoped Classical

variable (C : CircuitParameters) {d : ℕ}

lemma meanTree_base (r σ : ℝ) :
    base (C.meanTree (d:=d) r σ)=fun z => (σ/2) • z.2.2 := by
  exact (literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=C.N) (nc:=C.nc) (Nc:=C.Nc)
    (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint).1

lemma meanCompiled_variation {r σ Lf Li : ℝ} (hr : 0<r) (hσ : 0<σ)
    (hψ : 0≤C.ψ) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hLf : 0≤Lf) (hLi : 0≤Li) (hsmall : Li*C.meanCenterBudget r σ≤1)
    (V : Point d → ℝ) (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hm : ∀r τ,P true r τ → ∀u v g,‖(M true r τ).program.run V (u,g)-(M true r τ).program.run V (v,g)‖≤Lf*‖u-v‖)
    (hmi : ∀r τ,P false r τ → ∀u v g,‖(M false r τ).program.run V (u,g)-(M false r τ).program.run V (v,g)‖≤Li*‖u-v‖)
    (n : ℝ) (hready : RootShiftReady C.D (C.meanCenterBudget r σ) C.Af
      (P true) (P false) (C.meanTree (d:=d) r σ) n) :
    let E := compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af
      (M true) (M false) (C.meanTree (d:=d) r σ) n
    let K := C.Af*Lf*(depth (C.meanTree (d:=d) r σ):ℝ)
    (∀x y Y G g,‖E.eval V (x,(Y,G)) g-E.eval V (y,(Y,G)) g‖≤K*‖x-y‖) ∧
    (∀x Y Z G g,‖E.eval V (x,(Y,G)) g-E.eval V (x,(Z,G)) g‖≤(K*r)*‖Y-Z‖) := by
  have hw := C.meanTree_actual_weights (d:=d) hr hσ hψ
  rw [←hAf,←hA] at hw
  have hT0 : 0<C.T := by linarith [C.T_lower]
  constructor
  · intro x y Y G g
    have he := compileDeclaredRoot_variation hLf hLi (norm_nonneg (x-y)) hsmall V P M hm hmi
      (C.meanTree r σ) n (x,(Y,G)) (y,(Y,G))
      (literalMean_variationX hr.le hT0 C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint x y Y G)
      (Bf:=0) (by rw [C.meanTree_base]; simp) hw.1 hw.2 hready g
    simpa only [add_zero] using he
  · intro x Y Z G g
    have he := compileDeclaredRoot_variation hLf hLi (mul_nonneg hr.le (norm_nonneg (Y-Z))) hsmall V P M hm hmi
      (C.meanTree r σ) n (x,(Y,G)) (x,(Z,G))
      (literalMean_variationY hr.le hT0 C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint x Y Z G)
      (Bf:=0) (by rw [C.meanTree_base]; simp) hw.1 hw.2 hready g
    simpa only [add_zero,mul_assoc] using he

lemma sampleCompiled_variation {r η Lf Li : ℝ} (hr : 0<r) (hη : 0<η) (hη1 : η≤1)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hLf : 0≤Lf) (hLi : 0≤Li) (hsmall : Li*C.sampleCenterBudget r≤1)
    (V : Point d → ℝ) (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hm : ∀r τ,P true r τ → ∀u v g,‖(M true r τ).program.run V (u,g)-(M true r τ).program.run V (v,g)‖≤Lf*‖u-v‖)
    (hmi : ∀r τ,P false r τ → ∀u v g,‖(M false r τ).program.run V (u,g)-(M false r τ).program.run V (v,g)‖≤Li*‖u-v‖)
    (n : ℝ) (hready : RootShiftReady C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r)
      (P true) (P false) (C.sampleTree (d:=d) r η hη hη1) n) :
    let E := compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r)
      (M true) (M false) (C.sampleTree (d:=d) r η hη hη1) n
    ∀x y z g,‖E.eval V (x,z) g-E.eval V (y,z) g‖≤
      (C.sampleFinalBudget r*Lf*(depth (C.sampleTree (d:=d) r η hη hη1):ℝ))*‖x-y‖ := by
  have hw := C.sampleTree_actual_weights (d:=d) hr hη hη1
  rw [←hAf,←hA] at hw
  have hp := sampleCorrelation_properties hη hη1
  have hT0 : 0<sampleCorrelation η := by linarith [hp.1]
  dsimp only
  intro x y z g
  have hg := literalSample_geometry (d:=d) (r:=r) (N:=C.N) (Nat.succ_pos C.n)
    hT0 hp.2.1 C.h_pos (C.sampleEndpoint η hη hη1)
  have he := compileDeclaredRoot_variation (Af:=C.sampleFinalBudget r) hLf hLi (norm_nonneg (x-y)) hsmall V P M hm hmi
    (C.sampleTree r η hη hη1) n (x,z) (y,z)
    (literalSample_variationX hr.le (Nat.succ_pos C.n) hT0 hp.2.1 C.h_pos (C.sampleEndpoint η hη hη1) x y z)
    (Bf:=0) (by unfold sampleTree; rw [hg.1]; simp) hw.1 hw.2 hready g
  simpa only [add_zero] using he

end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
