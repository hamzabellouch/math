import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.MeanCorrect
import OAI.Probability.LogConcave.Sampling.PairGauge

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory ProbabilityTheory MeanTree Coupling SeedCompiler
open scoped Classical BigOperators NNReal

variable {d : ℕ}

lemma MeanBudget.shiftInvariant {B : ℕ} {r : ℝ} {S : SeedProgram d}
    (h : MeanBudget B r S) (F : Point d → ℝ) :
    ShiftInvariant r S.shift (fun c g => S.program.run F (c,g)) := by
  intro x Δ g
  exact (h.equiv Δ).run F (x,g)

namespace CircuitParameters
variable (C : CircuitParameters)
lemma meanCompiled_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki ef ei r σ : ℝ} (hs : MeanSize lam q r σ) (hl : q≤1/2)
    (hL : (lam:ℝ)*r≤1) (hD : 0<C.D) (hψ : 0≤C.ψ)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0≤Kf) (hKi : 0≤Ki)
    (hsmall : (lam:ℝ)*C.meanCenterBudget r σ*(2*Real.pi+2)≤1)
    (hcon : 4*(C.meanCenterBudget r σ)^2*((lam:ℝ)*Ki)^2≤1)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ)≤C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (x Y G : Point d) :
    let E := compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi
      (C.meanTree (d:=d) r σ) (Real.sqrt 3*σ/2)
    SquaredAt (gaussianTape d E.slots) (stdGaussian (Point d)) (E.eval F (x,(Y,G)))
      (fun g => (C.meanTree r σ).eval F (x,(Y,G))+(Real.sqrt 3*σ/2) • g)
      ((2*C.Af^2*((lam:ℝ)*Kf)^2*(r/(2*C.D))^2*ei^2+(Real.sqrt 3*σ/2)^2*ef^2/2)*
        (2*(depth (C.meanTree (d:=d) r σ):ℝ)*pairGauge (circuitD F x) (Y,G))^2) := by
  have hr := hs.1
  have hn := hs.2.2.1
  let P : Bool → ℝ → ℝ → Prop := fun s => if s then
    MeanSize lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) else
    MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2)))
  let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
  have hb (s : Bool) (r τ : ℝ) := hbudget s r τ
  have hV : Measurable (firstOrderReply F) := hF.smooth.continuous.measurable.prodMk
    hF.gradient_lipschitz.continuous.measurable
  have hv := C.meanTree_valid (d:=d) lam.coe_nonneg hs hD hψ hA hAf
  have hw := C.meanTree_actual_weights (d:=d) hs.1 hs.2.2.1 hψ
  rw [←hAf,←hA] at hw
  have hg := (literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=C.N) (nc:=C.nc) (Nc:=C.Nc)
    (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint).2
  have hrs : centers (fun r' _ => 0≤r' ∧ r'≤r) (C.meanTree (d:=d) r σ) :=
    centers_mono _ (fun r' b hb => ⟨(hb.radius_pos hs.1 (by linarith [C.T_lower]) C.T_upper).le,
      (hb.radius hs.1.le (by linarith [C.T_lower]) C.T_upper).2⟩) hg
  exact compileDeclaredRoot_normalized F F hV hD
    (by unfold meanCenterBudget; rw [hA]; positivity [C.actualA_pos])
    (by rw [hAf]; exact C.actualAf_pos) (mul_nonneg lam.coe_nonneg hKi) (mul_nonneg lam.coe_nonneg hKf)
    hcon P M (fun s r τ _ => (hb s r τ).shiftInvariant F)
    (fun s r τ _ => (hb s r τ).energy.trans hBD) hi.lip hf.lip hi.error hf.error
    (C.meanTree r σ) (x,(Y,G)) hv hw.2 hrs
    (C.meanTree_centerValues hF hs.1 hs.2.2.1 hψ hA (hs.2.2.2.1.trans hl) hL hsmall x Y G)

lemma sampleCompiled_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki ef ei r η : ℝ} (hs : SampleSize lam q r η) (hl : q≤1/2)
    (hL : (lam:ℝ)*r≤1) (hRη : Real.sqrt (1-C.T^2)≤η) (hD : 0<C.D)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0≤Kf) (hKi : 0≤Ki)
    (hsmall : (lam:ℝ)*C.sampleCenterBudget r*(2*Real.pi+2)≤1)
    (hcon : 4*(C.sampleCenterBudget r)^2*((lam:ℝ)*Ki)^2≤1)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ)≤C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (x Y : Point d) :
    let E := compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi
      (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1) (η/Real.sqrt 2)
    SquaredAt (gaussianTape d E.slots) (stdGaussian (Point d)) (E.eval F (x,Y))
      (fun g => (C.sampleTree r η hs.2.2.1 hs.2.2.2.1).eval F (x,Y)+(η/Real.sqrt 2) • g)
      ((2*(C.sampleFinalBudget r)^2*((lam:ℝ)*Kf)^2*(r/(2*C.D))^2*ei^2+(η/Real.sqrt 2)^2*ef^2/2)*
        ((depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ)*anchorGauge (circuitD F x) Y)^2) := by
  have hr := hs.1
  have hn := hs.2.2.1
  let P : Bool → ℝ → ℝ → Prop := fun s => if s then
    MeanSize lam ((1+4*C.Af)*q) else MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2)))
  let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
  have hb (s : Bool) (r τ : ℝ) := hbudget s r τ
  have hV : Measurable (firstOrderReply F) := hF.smooth.continuous.measurable.prodMk
    hF.gradient_lipschitz.continuous.measurable
  have hv := C.sampleTree_valid (d:=d) lam.coe_nonneg hs C.residual_pos hRη hD hA hAf
  have hw := C.sampleTree_actual_weights (d:=d) hs.1 hs.2.2.1 hs.2.2.2.1
  rw [←hAf,←hA] at hw
  have hp := sampleCorrelation_properties hs.2.2.1 hs.2.2.2.1
  have hg := (literalSample_geometry (d:=d) (r:=r) (N:=C.N) (Nat.succ_pos C.n)
    (by linarith [hp.1]) hp.2.1 C.h_pos (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1)).2
  have hrs : centers (fun r' _ => 0≤r' ∧ r'≤r) (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1) :=
    centers_mono _ (fun r' b hb => ⟨(hb.radius_pos hs.1 (by linarith [hp.1]) hp.2.1).le,
      (hb.radius hs.1.le (by linarith [hp.1]) hp.2.1).2⟩) hg
  have hl' : (lam:ℝ)*r^2≤1/2 := hs.2.2.2.2.trans
    ((mul_le_of_le_one_right (hs.nonneg lam.coe_nonneg) hs.2.2.2.1).trans hl)
  exact compileDeclaredRoot_normalized F F hV hD
    (by unfold sampleCenterBudget; rw [hA]; positivity [C.actualA_pos])
    (by unfold sampleFinalBudget; rw [hAf]; positivity [C.actualAf_pos])
    (mul_nonneg lam.coe_nonneg hKi) (mul_nonneg lam.coe_nonneg hKf)
    hcon P M (fun s r τ _ => (hb s r τ).shiftInvariant F)
    (fun s r τ _ => (hb s r τ).energy.trans hBD) hi.lip hf.lip hi.error hf.error
    (C.sampleTree r η hs.2.2.1 hs.2.2.2.1) (x,Y) hv hw.2 hrs
    (C.sampleTree_centerValues hF hs.1 hs.2.2.1 hs.2.2.2.1 hA hl' hL hsmall x Y)
end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree MeasureTheory
open scoped Classical

lemma physicalCoefficient_bound {lam r s D Af K ei ef q n : ℝ}
    (hl : 0 ≤ lam) (hr : 0 ≤ r) (hs : 0 < s) (hD : 1 ≤ D) (hAf : 0 ≤ Af)
    (hK : 0 ≤ K) (hi : 0 ≤ ei) (hf : 0 ≤ ef) (hq : lam*r ≤ q*s)
    (hn : 0 ≤ n) (hns : n ≤ s) :
    2*Af^2*(lam*K)^2*(r/(2*D))^2*ei^2+n^2*ef^2/2 ≤
      2*s^2*(Af*K*q*ei+ef)^2 := by
  have hD0 : 0 < 2*D := by linarith
  have hq0 : 0 ≤ q := by nlinarith [mul_nonneg hl hr]
  have hab : lam*r/(2*D) ≤ q*s := by
    apply (div_le_iff₀ hD0).2
    have hh := mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ 2*D) (mul_nonneg hq0 hs.le)
    nlinarith
  have ha : 0 ≤ Af*K*(lam*r/(2*D))*ei := by positivity
  have hb : Af*K*(lam*r/(2*D))*ei ≤ s*(Af*K*q*ei) := by
    have hh := mul_le_mul_of_nonneg_left hab (show 0 ≤ Af*K*ei by positivity)
    nlinarith
  have hc : n*ef ≤ s*ef := mul_le_mul_of_nonneg_right hns hf
  have ha2 := pow_le_pow_left₀ ha hb 2
  have hb2 := pow_le_pow_left₀ (mul_nonneg hn hf) hc 2
  have hid : Af^2*(lam*K)^2*(r/(2*D))^2*ei^2=(Af*K*(lam*r/(2*D))*ei)^2 := by ring
  have hid2 : 2*Af^2*(lam*K)^2*(r/(2*D))^2*ei^2=2*(Af*K*(lam*r/(2*D))*ei)^2 := by nlinarith [hid]
  rw [hid2]
  nlinarith [mul_nonneg (show 0 ≤ Af*K*q*ei by positivity) hf]

lemma physicalError_bound {c s a dep ρ : ℝ} (_hs : 0 ≤ s) (_ha : 0 ≤ a) (hd : 0 ≤ dep)
    (hc : c ≤ 2*s^2*a^2) :
    c*(dep*ρ)^2 ≤ (2*s*(1+dep)*a)^2*ρ^2 := by
  have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg (dep*ρ))
  have hdep : 2*dep^2 ≤ (2*(1+dep))^2 := by nlinarith
  have hh' := mul_le_mul_of_nonneg_right hdep (show 0 ≤ s^2*a^2*ρ^2 by positivity)
  nlinarith

end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree MeasureTheory ProbabilityTheory Coupling SeedCompiler
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

lemma meanCompiled_scaled {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki ef ei r σ : ℝ} (hs : MeanSize lam q r σ) (hl : q ≤ 1/2)
    (hL : (lam:ℝ)*r ≤ 1) (hD : 1 ≤ C.D) (hψ : 0 ≤ C.ψ)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0 ≤ Kf) (hKi : 0 ≤ Ki) (hef : 0 ≤ ef) (hei : 0 ≤ ei)
    (hsmall : (lam:ℝ)*C.meanCenterBudget r σ*(2*Real.pi+2) ≤ 1)
    (hcon : 4*(C.meanCenterBudget r σ)^2*((lam:ℝ)*Ki)^2 ≤ 1)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ) ≤ C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (x Y G : Point d) :
    let E := compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi
      (C.meanTree (d:=d) r σ) (Real.sqrt 3*σ/2)
    let a := 2*(1+2*(depth (C.meanTree (d:=d) r σ):ℝ))*(C.Af*Kf*q*ei+ef)
    SquaredAt (gaussianTape d E.slots) (stdGaussian (Point d)) (E.eval F (x,(Y,G)))
      (fun g => (C.meanTree r σ).eval F (x,(Y,G))+(Real.sqrt 3*σ/2) • g)
      ((σ*a)^2*(pairGauge (circuitD F x) (Y,G))^2) := by
  have hAf0 : 0 ≤ C.Af := by rw [hAf]; exact C.actualAf_pos.le
  have hn : Real.sqrt 3*σ/2 ≤ σ := by
    have hh : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg (3:ℝ)]
    nlinarith [mul_le_mul_of_nonneg_right hh hs.2.2.1.le]
  have hc := physicalCoefficient_bound lam.coe_nonneg hs.1.le hs.2.2.1 hD hAf0 hKf hei hef
    hs.2.2.2.2 (show 0 ≤ Real.sqrt 3*σ/2 by positivity [hs.2.2.1]) hn
  have hb := physicalError_bound hs.2.2.1.le
    (show 0 ≤ C.Af*Kf*q*ei+ef by positivity [hs.nonneg lam.coe_nonneg])
    (show 0 ≤ 2*(depth (C.meanTree (d:=d) r σ):ℝ) by positivity)
    (ρ:=pairGauge (circuitD F x) (Y,G)) hc
  have hp := C.meanCompiled_squared hF hs hl hL (by linarith) hψ hA hAf hKf hKi hsmall hcon
    Mf Mi B hBD hbudget hf hi x Y G
  apply hp.mono
  convert hb using 1
  ring

lemma sampleCompiled_scaled {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki ef ei r η : ℝ} (hs : SampleSize lam q r η) (hl : q ≤ 1/2)
    (hL : (lam:ℝ)*r ≤ 1) (hRη : Real.sqrt (1-C.T^2) ≤ η) (hD : 1 ≤ C.D)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0 ≤ Kf) (hKi : 0 ≤ Ki) (hef : 0 ≤ ef) (hei : 0 ≤ ei)
    (hsmall : (lam:ℝ)*C.sampleCenterBudget r*(2*Real.pi+2) ≤ 1)
    (hcon : 4*(C.sampleCenterBudget r)^2*((lam:ℝ)*Ki)^2 ≤ 1)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ) ≤ C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (x Y : Point d) :
    let E := compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi
      (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1) (η/Real.sqrt 2)
    let a := 2*(1+(depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ))*(C.Af*Kf*q*ei+ef)
    SquaredAt (gaussianTape d E.slots) (stdGaussian (Point d)) (E.eval F (x,Y))
      (fun g => (C.sampleTree r η hs.2.2.1 hs.2.2.2.1).eval F (x,Y)+(η/Real.sqrt 2) • g)
      ((η*a)^2*(anchorGauge (circuitD F x) Y)^2) := by
  have hAf0 : 0 ≤ C.Af := by rw [hAf]; exact C.actualAf_pos.le
  have hn : η/Real.sqrt 2 ≤ η := by
    exact div_le_self hs.2.2.1.le (by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)])
  have hc := physicalCoefficient_bound (mul_nonneg lam.coe_nonneg hs.1.le) hs.1.le hs.2.2.1 hD hAf0 hKf hei hef
    (show ((lam:ℝ)*r)*r ≤ q*η by nlinarith [hs.2.2.2.2])
    (show 0 ≤ η/Real.sqrt 2 by positivity [hs.2.2.1]) hn
  have hb := physicalError_bound hs.2.2.1.le
    (show 0 ≤ C.Af*Kf*q*ei+ef by positivity [hs.nonneg lam.coe_nonneg])
    (show 0 ≤ (depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ) by positivity)
    (ρ:=anchorGauge (circuitD F x) Y) hc
  have hp := C.sampleCompiled_squared hF hs hl hL hRη (by linarith) hA hAf hKf hKi hsmall hcon
    Mf Mi B hBD hbudget hf hi x Y
  apply hp.mono
  convert hb using 1 <;> (try unfold sampleFinalBudget) <;> ring
end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
