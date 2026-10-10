import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.MeanSize
import OAI.Probability.LogConcave.Sampling.LogMeshCountRate

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree MeasureTheory Quadrature
open scoped Classical NNReal

variable {d : ℕ}

lemma MeanSize.mono {lam q q' r σ : ℝ} (h : MeanSize lam q r σ) (hq : q≤q') :
    MeanSize lam q' r σ :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1.trans hq,
    h.2.2.2.2.trans (mul_le_mul_of_nonneg_right hq h.2.2.1.le)⟩

lemma SampleSize.mono {lam q q' r η : ℝ} (h : SampleSize lam q r η) (hq : q≤q') :
    SampleSize lam q' r η :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,
    h.2.2.2.2.trans (mul_le_mul_of_nonneg_right hq h.2.2.1.le)⟩

lemma final_mean_size {lam q r σ R Af : ℝ} (hlam : 0≤lam)
    (h : MeanSize lam q r σ) (hR : 0<R) (hR1 : R≤1) (hAf : 0<Af) :
    MeanSize lam ((1+4*Af)*R*q) (r*R) (declaredNoise (Real.sqrt 3*σ/2) Af) := by
  have hr := h.1
  have hσ := h.2.2.1
  have hq := h.nonneg hlam
  have hroot : 1≤Real.sqrt 3 := by norm_num
  have hn : 0<declaredNoise (Real.sqrt 3*σ/2) Af := by unfold declaredNoise; positivity
  have hrR : r*R≤r := mul_le_of_le_one_right h.1.le hR1
  have hR2 : R^2≤R := by nlinarith
  have hsq := mul_le_mul_of_nonneg_right h.2.2.2.1 (sq_nonneg R)
  have hqR := mul_le_mul_of_nonneg_left hR2 hq
  have hAfR : R*q≤(1+4*Af)*R*q := by nlinarith [mul_nonneg hR.le hq]
  refine ⟨mul_pos h.1 hR,hrR.trans h.2.1,hn,?_,?_⟩
  · nlinarith [hsq]
  · have hσ : σ/(4*Af)≤declaredNoise (Real.sqrt 3*σ/2) Af := by
      unfold declaredNoise
      have hh := mul_le_mul_of_nonneg_right hroot h.2.2.1.le
      apply (le_div_iff₀ (by positivity : 0<2*Af)).2
      calc
        σ/(4*Af)*(2*Af)=σ/2 := by field_simp; ring
        _≤Real.sqrt 3*σ/2 := by linarith
    have hs := mul_le_mul_of_nonneg_right h.2.2.2.2 hR.le
    have ht := mul_le_mul_of_nonneg_left hσ (show 0≤4*Af*R*q by positivity)
    have hid : (4*Af*R*q)*(σ/(4*Af))=q*σ*R := by field_simp
    rw [hid] at ht
    have he : 4*Af*R*q≤(1+4*Af)*R*q := by nlinarith [mul_nonneg hR.le hq]
    have hh := mul_le_mul_of_nonneg_right he hn.le
    nlinarith

lemma final_sample_size {lam q r η r' Af : ℝ} (hlam : 0≤lam)
    (h : SampleSize lam q r η) (hr' : 0<r') (hhi : r'≤r) (hAf : 0<Af) :
    MeanSize lam ((1+4*Af)*q) r' (declaredNoise (η/Real.sqrt 2) (Af*r)) := by
  have hr := h.1
  have hη0 := h.2.2.1
  have hq := h.nonneg hlam
  have hs2 : 0<Real.sqrt 2 := by positivity
  have hs21 : Real.sqrt 2≤2 := by norm_num
  have hn : 0<declaredNoise (η/Real.sqrt 2) (Af*r) := by unfold declaredNoise; positivity
  have hl : lam*r^2≤q := h.2.2.2.2.trans (mul_le_of_le_one_right hq h.2.2.2.1)
  have hqf : q≤(1+4*Af)*q := by nlinarith
  refine ⟨hr',hhi.trans h.2.1,hn,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr'.le hhi 2) hlam).trans (hl.trans hqf)
  · have hη : η/(4*Af*r)≤declaredNoise (η/Real.sqrt 2) (Af*r) := by
      unfold declaredNoise
      apply (le_div_iff₀ (by positivity : 0<2*(Af*r))).2
      calc
        η/(4*Af*r)*(2*(Af*r))=η/2 := by field_simp [hr.ne']; ring
        _≤η/Real.sqrt 2 := div_le_div_of_nonneg_left h.2.2.1.le hs2 hs21
    have hh := mul_le_mul_of_nonneg_right hη (show 0≤4*Af*q by positivity)
    have hid : (η/(4*Af*r))*(4*Af*q)=q*η/r := by field_simp
    rw [hid] at hh
    have hs : lam*r≤q*η/r := (le_div_iff₀ h.1).2 (by nlinarith [h.2.2.2.2])
    have hm := mul_le_mul_of_nonneg_left hhi hlam
    have he := mul_le_mul_of_nonneg_right (show 4*Af*q≤(1+4*Af)*q by nlinarith) hn.le
    nlinarith

namespace CircuitParameters
variable (C : CircuitParameters)

lemma residual_pos : 0<Real.sqrt (1-C.T^2) := by
  apply Real.sqrt_pos.mpr
  nlinarith [C.T_lower,C.T_upper]
lemma residual_le_one : Real.sqrt (1-C.T^2)≤1 := by
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by norm_num,by nlinarith [sq_nonneg C.T]⟩

theorem meanTree_valid {lam q r σ : ℝ} (hlam : 0≤lam) (hs : MeanSize lam q r σ)
    (hD : 0<C.D) (hψ : 0≤C.ψ) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf) :
    DeclaredRootValid C.D (C.meanCenterBudget r σ) C.Af
      (MeanSize lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q))
      (MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))))
      (C.meanTree (d:=d) r σ) (Real.sqrt 3*σ/2) := by
  have hA0 : 0<C.A := hA ▸ C.actualA_pos
  have hAf0 : 0<C.Af := hAf ▸ C.actualAf_pos
  have hr := hs.1
  have hσ := hs.2.2.1
  have hb : 0<C.meanCenterBudget r σ := by unfold meanCenterBudget; positivity
  have hR := C.residual_pos
  have hq := hs.nonneg hlam
  have hw := C.meanTree_actual_weights (d:=d) hs.1 hs.2.2.1 hψ
  rw [←hA,←hAf] at hw
  have hg := (literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=C.N) (nc:=C.nc) (Nc:=C.Nc)
    (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint).2
  apply declaredRootValid_of_radius_bounds hD (mul_pos hs.1 hR) _ _ _ (by positivity) hw.1 hw.2
  · exact centers_mono _ (fun r' b h => h.radius hs.1.le (by linarith [C.T_lower]) C.T_upper) hg
  · have hf := meanCircuit_final_radius (d:=d) r C.T C.h C.ψ (σ/2) C.n C.m C.N C.nc C.Nc C.meanEndpoint
      (anchor Prod.fst (by fun_prop)) (anchor (fun z : MeanInput d => z.2.1) (by fun_prop))
      (fun z : MeanInput d => z.2.2) (by fun_prop)
    cases he : C.meanTree (d:=d) r σ with | node k b hb a rr cc =>
      change ∀i, MeanSize _ _ (rr i) _
      have hf' : ∀i,rr i=r*Real.sqrt (1-C.T^2) := by
        change rootScales (fun r' => r'=r*Real.sqrt (1-C.T^2)) (C.meanTree r σ) at hf
        rw [he] at hf
        exact hf
      intro i
      rw [hf' i]
      exact final_mean_size hlam hs hR C.residual_le_one hAf0
  · intro r' n hlo hhi hn _
    apply (internal_meanSize hlam hq hs.1 hs.2.1 hR hD hb hs.2.2.2.1 hlo hhi hn).mono
    have hsmall := C.meanCenterBudget_small hs hA0.le
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0≤4*C.D/Real.sqrt (1-C.T^2) by positivity)
    have hx : 0≤C.D*C.A*q/Real.sqrt (1-C.T^2) := by positivity
    nlinarith [show (4*C.D/Real.sqrt (1-C.T^2))*(lam*C.meanCenterBudget r σ)=
      4*C.D*lam*C.meanCenterBudget r σ/Real.sqrt (1-C.T^2) by ring,
      show (4*C.D/Real.sqrt (1-C.T^2))*(2*C.A*q)=8*(C.D*C.A*q/Real.sqrt (1-C.T^2)) by ring,
      show q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))=q+16*(C.D*C.A*q/Real.sqrt (1-C.T^2)) by ring]

theorem sampleTree_valid {lam q r η R : ℝ} (hlam : 0≤lam) (hs : SampleSize lam q r η)
    (hR : 0<R) (hRη : R≤η) (hD : 0<C.D)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf) :
    DeclaredRootValid C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r)
      (MeanSize lam ((1+4*C.Af)*q))
      (MeanSize lam (q*(1+16*C.D*C.A/R)))
      (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1) (η/Real.sqrt 2) := by
  have hA0 : 0<C.A := hA ▸ C.actualA_pos
  have hAf0 : 0<C.Af := hAf ▸ C.actualAf_pos
  have hr := hs.1
  have hη := hs.2.2.1
  have hq := hs.nonneg hlam
  have hb : 0<C.sampleCenterBudget r := by unfold sampleCenterBudget; positivity
  have hw := C.sampleTree_actual_weights (d:=d) hr hη hs.2.2.2.1
  rw [←hA,←hAf] at hw
  have hp := sampleCorrelation_properties hη hs.2.2.2.1
  have hg := (literalSample_geometry (d:=d) (r:=r) (N:=C.N) (Nat.succ_pos C.n)
    (by linarith [hp.1]) hp.2.1 C.h_pos (C.sampleEndpoint η hη hs.2.2.2.1)).2
  have hrad : centers (fun r' (_ : SampleInput d → Point d) => r*(R/4)≤r' ∧ r'≤r)
      (C.sampleTree r η hη hs.2.2.2.1) := by
    apply centers_mono _ (fun r' b h => ?_) hg
    have hh := h.radius hr.le (by linarith [hp.1]) hp.2.1
    have hlow := sampleCorrelation_radius_lower hη hs.2.2.2.1
    exact ⟨(mul_le_mul_of_nonneg_left (by linarith : R/4≤Real.sqrt (1-(sampleCorrelation η)^2)) hr.le).trans hh.1,hh.2⟩
  have hfinal : rootScales (fun r' => MeanSize lam ((1+4*C.Af)*q) r'
      (declaredNoise (η/Real.sqrt 2) (C.sampleFinalBudget r)))
      (C.sampleTree (d:=d) r η hη hs.2.2.2.1) := by
    cases he : C.sampleTree (d:=d) r η hη hs.2.2.2.1 with | node k b hb a rr cc =>
      rw [he] at hrad
      intro i
      exact final_sample_size hlam hs ((by positivity : 0<r*(R/4)).trans_le (hrad i).1.1)
        (hrad i).1.2 hAf0
  apply declaredRootValid_of_radius_bounds hD (by positivity : 0<r*(R/4)) _ _ _
    (by positivity) hw.1 hw.2 hrad hfinal
  intro r' n hlo hhi hn _
  have hl : lam*r^2≤q := hs.2.2.2.2.trans (mul_le_of_le_one_right hq hs.2.2.2.1)
  apply (internal_meanSize hlam hq hr hs.2.1 (by positivity : 0<R/4) hD hb hl hlo hhi hn).mono
  have hsml := C.sampleCenterBudget_small hlam hs hA0.le
  have hh := mul_le_mul_of_nonneg_left hsml (show 0≤16*C.D/R by positivity)
  calc
    q+4*C.D*lam*C.sampleCenterBudget r/(R/4)
        = q+(16*C.D/R)*(lam*C.sampleCenterBudget r) := by ring
    _≤q+(16*C.D/R)*(C.A*q) := add_le_add le_rfl hh
    _=q*(1+16*C.D*C.A/R) := by ring

lemma mean_anchor_size {lam q r σ : ℝ} (hlam : 0≤lam) (hs : MeanSize lam q r σ)
    (hRT : Real.sqrt (1-C.T^2)≤C.T) :
    SampleSize lam (q/Real.sqrt (1-C.T^2)) r (Real.sqrt (1-C.T^2)/C.T) := by
  have hT : 0<C.T := by linarith [C.T_lower]
  have hR := C.residual_pos
  have hq := hs.nonneg hlam
  refine ⟨hs.1,hs.2.1,div_pos hR hT,(div_le_one hT).2 hRT,?_⟩
  calc
    lam*r^2≤q := hs.2.2.2.1
    _≤q/C.T := (le_div_iff₀ hT).2 (mul_le_of_le_one_right hq C.T_upper.le)
    _=(q/Real.sqrt (1-C.T^2))*(Real.sqrt (1-C.T^2)/C.T) := by field_simp

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory ProbabilityTheory Coupling
open scoped Classical NNReal

variable {d : ℕ}

structure MeanCorrect (F : Point d → ℝ) (lam q K e : ℝ)
    (M : ℝ → ℝ → SeedProgram d) : Prop where
  lip : ∀r σ,MeanSize lam q r σ → ∀x y g,
    ‖(M r σ).program.run F (x,g)-(M r σ).program.run F (y,g)‖≤lam*K*‖x-y‖
  error : ∀r σ,MeanSize lam q r σ → ∀x,
    SquaredAt (gaussianTape d (M r σ).slots) (stdGaussian (Point d))
      (fun g => (M r σ).program.run F (x,g))
      (fun g => primitiveExpectedField F x r+σ • g) (σ^2*e^2*(circuitD F x)^2)

structure SampleCorrect (F : Point d → ℝ) (lam q K e : ℝ) (ηmin : ℝ)
    (S : ℝ → ℝ → ReservedProgram d) : Prop where
  lip : ∀r η,SampleSize lam q r η → ηmin≤η → ∀x y g,
    ‖(S r η).pre.run F (x,g)-(S r η).pre.run F (y,g)‖≤lam*r*K*‖x-y‖
  error : ∀r η,SampleSize lam q r η → ηmin≤η → ∀x,
    SquaredAt (gaussianTape d (S r η).slots)
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
      (fun g => (S r η).pre.run F (x,g))
      (fun z => z.1+(Real.sqrt 3*η/2) • z.2) (e^2*(circuitD F x)^2)

lemma primitive_terminal_envelope (F : Point d → ℝ) (x : Point d) {r c : ℝ}
    (hr : 0≤r) (hr1 : r≤1) (hc : 0≤c) :
    2*(Real.pi*Real.sqrt d+c*r*‖primitiveField F x r 0‖)^2+2*d≤
      (2*(Real.pi+c)^2+2)*(circuitD F x)^2 := by
  rw [field_zero_eq_gradient]
  have hs := sqrt_le_circuitD F x
  have hg : ‖gradient F x‖≤circuitD F x := le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hcr := mul_le_mul_of_nonneg_left hr1 hc
  have hcg := mul_le_mul_of_nonneg_left hg hc
  have hrG := mul_le_mul_of_nonneg_right hcr (norm_nonneg (gradient F x))
  have hp := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
  have hu : Real.pi*Real.sqrt d+c*r*‖gradient F x‖≤(Real.pi+c)*circuitD F x := by nlinarith
  have hu2 := pow_le_pow_left₀ (show 0≤Real.pi*Real.sqrt d+c*r*‖gradient F x‖ by positivity) hu 2
  have hd2 := pow_le_pow_left₀ (Real.sqrt_nonneg (d:ℝ)) hs 2
  rw [Real.sq_sqrt (Nat.cast_nonneg d)] at hd2
  nlinarith

lemma terminalMean_correct {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q : ℝ} (hq : q≤1/2) :
    MeanCorrect F lam q 1 ((4*(Real.pi+2))*q) (terminalMeanProgram d) := by
  constructor
  · intro r σ hs x y g
    change ‖(SeedCompiler.terminalMean d r σ).run F (x,g)-
      (SeedCompiler.terminalMean d r σ).run F (y,g)‖≤(lam:ℝ)*1*‖x-y‖
    simp only [mul_one]
    exact (SeedCompiler.terminalMean_fixedSeed_lip hF.gradient_lipschitz r σ g).norm_sub_le x y
  · intro r σ hs x
    apply (terminalMeanProgram_squared hF x hs.1.le (hs.2.2.2.1.trans hq) σ).mono
    have hb := primitive_terminal_envelope F x hs.1.le hs.2.1 (c:=1) (by norm_num)
    simp only [one_mul] at hb
    have hq0 := hs.nonneg lam.coe_nonneg
    have hr := hs.1
    have hsq := pow_le_pow_left₀ (show 0≤(lam:ℝ)*r by positivity) hs.2.2.2.2 2
    have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (2*((lam:ℝ)*r)))
    have hc : 4*(2*(Real.pi+1)^2+2)≤(4*(Real.pi+2))^2 := by nlinarith [Real.pi_pos]
    have h₁ := mul_le_mul_of_nonneg_right hsq (show 0≤4*(2*(Real.pi+1)^2+2)*(circuitD F x)^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hc (show 0≤(q*σ)^2*(circuitD F x)^2 by positivity)
    nlinarith

lemma terminalSample_correct {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q : ℝ} (hq : q≤1/2) (ηmin : ℝ) :
    SampleCorrect F lam q 1 ((2*terminalTransportConstant*(Real.pi+3))*q) ηmin
      (terminalReservedProgram d) := by
  constructor
  · intro r η hs _ x y g
    have hh := terminalReservedProgram_lipschitz r η hF x y g
    rw [abs_of_pos hs.1] at hh
    simpa only [mul_one,mul_comm r (lam:ℝ)] using hh
  · intro r η hs _ x
    have hq0 := hs.nonneg lam.coe_nonneg
    have hl : (lam:ℝ)*r^2≤q := hs.2.2.2.2.trans
      (mul_le_of_le_one_right hq0 hs.2.2.2.1)
    apply (terminalReservedProgram_squared hF x hs.1.le (hl.trans hq) η).mono
    have hb := primitive_terminal_envelope F x hs.1.le hs.2.1 (c:=2) (by norm_num)
    have hsq := pow_le_pow_left₀ (show 0≤(lam:ℝ)*r^2 by positivity) hl 2
    have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (terminalTransportConstant*((lam:ℝ)*r^2)))
    have hc : 2*(Real.pi+2)^2+2≤(2*(Real.pi+3))^2 := by nlinarith [Real.pi_pos]
    have h₁ := mul_le_mul_of_nonneg_right hsq (show 0≤terminalTransportConstant^2*(2*(Real.pi+2)^2+2)*(circuitD F x)^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hc (show 0≤terminalTransportConstant^2*q^2*(circuitD F x)^2 by positivity)
    nlinarith
end LogConcaveSampling.OracleCompiler

end

end

end OAI
