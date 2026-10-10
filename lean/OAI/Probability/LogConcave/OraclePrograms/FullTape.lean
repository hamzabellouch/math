import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.MeanCorrect
import OAI.Probability.LogConcave.OraclePrograms.CalibratedMeanCircuit
import OAI.Probability.LogConcave.OraclePrograms.PairDistBounds
import OAI.Probability.LogConcave.OraclePrograms.ShiftInvariant
import OAI.Probability.LogConcave.Sampling.PrependTape
import OAI.Probability.LogConcave.Dynamics.ProbabilityFlowGrowth

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.ReservedProgram
open MeasureTheory ProbabilityTheory Function Coupling
open scoped Classical NNReal

variable {d : ℕ}

def fullTape (k : ℕ) (z : (Fin k → Point d) × Point d) : Fin (k+1) → Point d :=
  Fin.append z.1 (fun _ => z.2)

lemma fullTape_preserving (k : ℕ) :
    MeasurePreserving (fullTape (d:=d) k) ((gaussianTape d k).prod (stdGaussian (Point d)))
      (gaussianTape d (k+1)) := by
  exact (MeanTree.appendSlots_preserving (stdGaussian (Point d)) k 1).comp
    ((MeasurePreserving.id _).prod (oneSlot_preserving (stdGaussian (Point d))))

lemma full_fixedSeed {V : Point d → ℝ} (S : ReservedProgram d) {K : ℝ}
    (h : ∀x y g,‖S.pre.run V (x,g)-S.pre.run V (y,g)‖≤K*‖x-y‖) :
    ∀x y g,‖S.full.program.run V (x,g)-S.full.program.run V (y,g)‖≤K*‖x-y‖ := by
  intro x y g
  have hx := full_run S V x g
  have hy := full_run S V y g
  rw [hx,hy,add_sub_add_right_eq_sub]
  exact h x y _

lemma anchor_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) (S : ReservedProgram d) {r T η B : ℝ}
    (hr : 0≤r) (hl : (lam:ℝ)*r^2<1) (hT : 0≤T)
    (hη : T*η=Real.sqrt (1-T^2)) (hreserve : S.reserve=η/2)
    (hpre : SquaredAt (gaussianTape d S.slots)
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
      (fun g => S.pre.run F (x,g)) (fun z => z.1+(Real.sqrt 3*η/2) • z.2) B) :
    SquaredAt (gaussianTape d S.full.slots) (interpolationLaw F x r T)
      (fun g => T • S.full.program.run F (x,g)) id (T^2*B) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr hl))
  have hV : Measurable (fun z => (F z,gradient F z)) :=
    hF.smooth.continuous.measurable.prodMk hF.gradient_lipschitz.continuous.measurable
  have hf : Measurable (fun g => S.pre.run F (x,g)) :=
    (S.pre.measurable_run F hV).comp (by fun_prop)
  have hfull : Measurable (fun g => T • S.full.program.run F (x,g)) := by
    have hh := (S.full.program.measurable_run F hV).comp (show Measurable (fun z : Fin S.full.slots → Point d => (x,z)) by fun_prop)
    fun_prop
  let H : Point d → Point d → Point d := fun a g => T • (a+S.reserve • g)
  have hh := hpre.shared_lipschitz (stdGaussian (Point d)) hf (by fun_prop) hT H (by fun_prop)
    (fun a b g => by simp only [H,←smul_sub,add_sub_add_right_eq_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hT]; exact le_rfl)
  have hnoise := smoothing_add_gaussian
    ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))) (gibbs (primitivePotential F x r))
    (fun z => z.1+(Real.sqrt 3*η/2) • z.2) id (by fun_prop) measurable_id
    (Real.sqrt 3*η/2) (η/2) η (by
      rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3),div_pow]; ring) rfl
  have hnoise' := congrArg (Measure.map (fun z : Point d => T • z)) hnoise
  rw [Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop)] at hnoise'
  have hlaw : (((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))).prod (stdGaussian (Point d))).map
      (fun z => H (z.1.1+(Real.sqrt 3*η/2) • z.1.2) z.2)=interpolationLaw F x r T := by
    convert hnoise' using 1
    · simp only [H,hreserve,comp_def]
    · simp only [comp_def,smul_add,smul_smul,hη,interpolationLaw,id_eq]
  have hp := hh.reindex (fullTape S.slots)
    (fun z => H (z.1.1+(Real.sqrt 3*η/2) • z.1.2) z.2)
    (fullTape_preserving S.slots).measurable (by fun_prop)
    (fun g : Fin (S.slots+1) → Point d => T • S.full.program.run F (x,g)) id hfull measurable_id
    (fun z => by rw [full_run]; simp only [fullTape,Fin.append_left,Fin.append_right,H])
    (fun _ => rfl)
  rw [(fullTape_preserving S.slots).map_eq,hlaw] at hp
  exact hp
end LogConcaveSampling.OracleCompiler.ReservedProgram

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeasureTheory ProbabilityTheory MeanTree Coupling Function
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

theorem meanFrom_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki Ks ef ei es ηmin r σ en : ℝ} (hd : 1 ≤ d)
    (hs : MeanSize lam q r σ) (hl : q ≤ 1/4) (hL : (lam:ℝ)*r ≤ 1)
    (hD : 1 ≤ C.D) (hψ : 0 ≤ C.ψ) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0 ≤ Kf) (hKi : 0 ≤ Ki) (hef : 0 < ef) (hei : 0 ≤ ei)
    (hsmall : (lam:ℝ)*C.meanCenterBudget r σ*(2*Real.pi+2) ≤ 1)
    (hcon : 4*(C.meanCenterBudget r σ)^2*((lam:ℝ)*Ki)^2 ≤ 1)
    (hRT : Real.sqrt (1-C.T^2) ≤ C.T) (hη : ηmin ≤ Real.sqrt (1-C.T^2)/C.T)
    (hm : C.m=C.n) (hnc : C.nc=C.n) (hNc : C.Nc=C.N)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (S : ℝ → ℝ → ReservedProgram d)
    (B : ℕ) (hBD : (B:ℝ) ≤ C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (hS : SampleCorrect F lam (q/Real.sqrt (1-C.T^2)) Ks es ηmin S)
    (hrsv : (S r (Real.sqrt (1-C.T^2)/C.T)).reserve=(Real.sqrt (1-C.T^2)/C.T)/2)
    (x : Point d)
    (hcert : CalibratedMeanCircuit (r:=r) (T:=C.T) (h:=C.h) (ψ:=C.ψ) (s:=σ/2)
      hF x hs.1 (by linarith [hs.2.2.2.1] : (lam:ℝ)*r^2 ≤ 1/2)
      (by linarith [C.T_lower]) C.T_upper C.h_pos C.n C.N (en^2)) :
    let dep := (depth (C.meanTree (d:=d) r σ):ℝ)
    let a := 2*(1+2*dep)*(C.Af*Kf*q*ei+ef)
    SquaredAt (gaussianTape d (C.meanFrom Mf Mi S r σ).slots) (stdGaussian (Point d))
      (fun g => (C.meanFrom Mf Mi S r σ).program.run F (x,g))
      (fun g => primitiveExpectedField F x r+σ • g)
      (2*(C.Af*((lam:ℝ)*Kf)*dep*r)^2*(C.T^2*(es^2*(circuitD F x)^2))+
        80*(σ*a)^2*((20+16*circuitGrowthConstant^2)*(circuitD F x)^2)+
        8*((σ/2)*circuitD F x)^2*en^2) := by
  let dep := (depth (C.meanTree (d:=d) r σ):ℝ)
  let a := 2*(1+2*dep)*(C.Af*Kf*q*ei+ef)
  let P : Bool → ℝ → ℝ → Prop := fun s => if s then
    MeanSize lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) else
    MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2)))
  let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
  let E := compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi
    (C.meanTree (d:=d) r σ) (Real.sqrt 3*σ/2)
  have hA0 : 0 < C.A := hA ▸ C.actualA_pos
  have hAf0 : 0 < C.Af := hAf ▸ C.actualAf_pos
  have hbud : 0 ≤ C.meanCenterBudget r σ := by unfold meanCenterBudget; positivity [hs.1,hs.2.2.1]
  have hLip : (lam:ℝ)*Ki*C.meanCenterBudget r σ ≤ 1 := by
    have hn : 0 ≤ (lam:ℝ)*Ki*C.meanCenterBudget r σ := by positivity
    nlinarith [sq_nonneg ((lam:ℝ)*Ki*C.meanCenterBudget r σ)]
  have hrad : (lam:ℝ)*r^2 ≤ 1/4 := hs.2.2.2.1.trans hl
  have hT : 0 ≤ C.T := by linarith [C.T_lower]
  have ha : 0 < a := by dsimp [a,dep]; positivity [hs.nonneg lam.coe_nonneg]
  have hv := C.meanTree_valid (d:=d) lam.coe_nonneg hs (by linarith) hψ hA hAf
  have hrdy := hv.shiftReady (P true) (P false) (fun _ _ h => h.1.ne')
    (fun _ _ h => h.1.ne') _ _
  have hpos := C.meanCompiled_variation hs.1 hs.2.2.1 hψ hA hAf
    (mul_nonneg lam.coe_nonneg hKf) (mul_nonneg lam.coe_nonneg hKi) hLip F P M hf.lip hi.lip
    (Real.sqrt 3*σ/2) hrdy
  obtain ⟨Lf,hLf,hfl⟩ := C.meanCompiled_anchor_lipschitz hs.1 hs.2.2.1 hψ hA hAf
    (mul_nonneg lam.coe_nonneg hKf) (mul_nonneg lam.coe_nonneg hKi) hLip F P M hf.lip hi.lip
    (Real.sqrt 3*σ/2) hrdy x
  obtain ⟨Lg,hgl⟩ := C.meanTree_anchor_lipschitz (σ:=σ) hF hs.1 hrad x
  have hc (z : Point d × Point d) := C.meanCompiled_scaled hF hs (by linarith) hL hD hψ hA hAf hKf hKi hef.le hei
    hsmall hcon Mf Mi B hBD hbudget hf hi x z.1 z.2
  have hanc := C.mean_anchor_size lam.coe_nonneg hs hRT
  have he := hS.error _ _ hanc hη x
  have hanc' := ReservedProgram.anchor_squared hF x _ hs.1.le (by linarith : (lam:ℝ)*r^2 < 1) hT
    (show C.T*(Real.sqrt (1-C.T^2)/C.T)=Real.sqrt (1-C.T^2) by field_simp [ne_of_gt (by linarith [C.T_lower] : 0<C.T)]) hrsv he
  let := interpolationLaw_probability hF x hs.1.le (by linarith : (lam:ℝ)*r^2 < 1) C.T
  obtain ⟨w,hw,hlaw,hwi,hnum⟩ := C.meanTree_numerical_noisy hF x hs.1 hrad hm hnc hNc hcert
  have hmoment := pairGauge_interpolation_moment hF x hs.1.le hs.2.1
    (by linarith : (lam:ℝ)*r^2 ≤ 1/2) hT C.T_upper hd
  let v := compileDeclaredRootShift C.D (C.meanCenterBudget r σ) C.Af Mf Mi
    (C.meanTree (d:=d) r σ) (Real.sqrt 3*σ/2) (C.meanDrift r σ hs.1)
  let anc := S r (Real.sqrt (1-C.T^2)/C.T)
  have hp := meanParent_squared hF x anc.full E (anc.extraShift (-2*Real.sqrt (1-C.T^2)/C.T)) v C.T
    (interpolationLaw F x r C.T) (fun z => (C.meanTree r σ).eval F (x,z)) w
    (primitiveExpectedField F x r) σ (Real.sqrt 3*σ/2) hgl.continuous.measurable hw
    (pairGauge (circuitD F x)) (one_le_pairGauge (circuitD_nonneg F x))
    (pairGauge_change _) hmoment.1
    (show 0 ≤ C.Af*((lam:ℝ)*Kf)*dep*r by positivity [hs.1]) hLf Lg.coe_nonneg
    (mul_pos hs.2.2.1 ha) hanc' (hpos.2 x) hfl
    (fun z z' => by simpa only [dist_eq_norm] using hgl.dist_le_mul z z')
    hc hwi hnum hlaw
  unfold meanFrom
  rw [dite_eq_left hs.1]
  apply hp.mono
  have hh := mul_le_mul_of_nonneg_left hmoment.2 (show 0 ≤ 80*(σ*a)^2 by positivity)
  calc
    _ ≤ 2*(C.Af*((lam:ℝ)*Kf)*dep*r)^2*(C.T^2*(es^2*(circuitD F x)^2))+
      80*(σ*a)^2*((20+16*circuitGrowthConstant^2)*(circuitD F x)^2)+
      8*((σ/2*circuitD F x)^2*en^2) := add_le_add (add_le_add le_rfl hh) le_rfl
    _ = _ := by ring
end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeasureTheory ProbabilityTheory MeanTree Coupling Function
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

theorem sampleFrom_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki ef ei r η en : ℝ} (hd : 1 ≤ d)
    (hs : SampleSize lam q r η) (hl : q ≤ 1/4) (hL : (lam:ℝ)*r ≤ 1)
    (hRη : Real.sqrt (1-C.T^2) ≤ η) (hD : 1 ≤ C.D)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0 ≤ Kf) (hKi : 0 ≤ Ki) (hef : 0 < ef) (hei : 0 ≤ ei)
    (hsmall : (lam:ℝ)*C.sampleCenterBudget r*(2*Real.pi+2) ≤ 1)
    (hcon : 4*(C.sampleCenterBudget r)^2*((lam:ℝ)*Ki)^2 ≤ 1)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ) ≤ C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (x : Point d)
    (hlr : (lam:ℝ)*r^2 ≤ 1/2)
    (hnumi : Integrable (fun Y => ‖sampleMeanCircuit F x r (sampleCorrelation η) C.h
      (C.n+1) C.N (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1) Y-
      (sampleCorrelation η)⁻¹ • fullProbabilityFlow hF x hs.1.le hlr (sampleCorrelation η) Y‖^2)
      (stdGaussian (Point d)))
    (hnum : (∫Y,‖sampleMeanCircuit F x r (sampleCorrelation η) C.h
      (C.n+1) C.N (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1) Y-
      (sampleCorrelation η)⁻¹ • fullProbabilityFlow hF x hs.1.le hlr (sampleCorrelation η) Y‖^2
      ∂stdGaussian (Point d)) ≤ (circuitD F x)^2*en^2) :
    let dep := (depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ)
    let a := 2*(1+dep)*(C.Af*Kf*q*ei+ef)
    SquaredAt (gaussianTape d (C.sampleFrom Mf Mi r η).slots)
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
      (fun g => (C.sampleFrom Mf Mi r η).pre.run F (x,g))
      (fun z => z.1+(Real.sqrt 3*η/2) • z.2)
      ((400*(η*a)^2+4*en^2)*(circuitD F x)^2) := by
  let dep := (depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ)
  let a := 2*(1+dep)*(C.Af*Kf*q*ei+ef)
  let P : Bool → ℝ → ℝ → Prop := fun s => if s then
    MeanSize lam ((1+4*C.Af)*q) else MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2)))
  let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
  let E := compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi
    (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1) (η/Real.sqrt 2)
  have hA0 : 0 < C.A := hA ▸ C.actualA_pos
  have hAf0 : 0 < C.Af := hAf ▸ C.actualAf_pos
  have hbud : 0 ≤ C.sampleCenterBudget r := by unfold sampleCenterBudget; positivity
  have hLip : (lam:ℝ)*Ki*C.sampleCenterBudget r ≤ 1 := by
    have hn : 0 ≤ (lam:ℝ)*Ki*C.sampleCenterBudget r := by positivity
    nlinarith [sq_nonneg ((lam:ℝ)*Ki*C.sampleCenterBudget r)]
  have hrad : (lam:ℝ)*r^2 ≤ 1/4 := hs.2.2.2.2.trans
    ((mul_le_of_le_one_right (hs.nonneg lam.coe_nonneg) hs.2.2.2.1).trans hl)
  have ha : 0 < a := by dsimp [a,dep]; positivity [hs.nonneg lam.coe_nonneg]
  have hv := C.sampleTree_valid (d:=d) lam.coe_nonneg hs C.residual_pos hRη (by linarith) hA hAf
  have hrdy := hv.shiftReady (P true) (P false) (fun _ _ h => h.1.ne') (fun _ _ h => h.1.ne') _ _
  obtain ⟨Lf,hLf,hfl⟩ := C.sampleCompiled_anchor_lipschitz hs.1 hs.2.2.1 hs.2.2.2.1 hA hAf
    (mul_nonneg lam.coe_nonneg hKf) (mul_nonneg lam.coe_nonneg hKi) hLip F P M hf.lip hi.lip
    (η/Real.sqrt 2) hrdy x
  obtain ⟨Lg,hgl⟩ := C.sampleTree_anchor_lipschitz hF hs.1 hs.2.2.1 hs.2.2.2.1 hrad x
  have heval : (fun Y => (C.sampleTree r η hs.2.2.1 hs.2.2.2.1).eval F (x,Y))=
      sampleMeanCircuit F x r (sampleCorrelation η) C.h (C.n+1) C.N
        (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1) := by
    funext Y; exact C.sampleTree_eval hF r η hs.2.2.1 hs.2.2.2.1 x Y
  rw [heval] at hgl
  have hc Y := C.sampleCompiled_scaled hF hs (by linarith) hL hRη hD hA hAf hKf hKi hef.le hei
    hsmall hcon Mf Mi B hBD hbudget hf hi x Y
  simp only [C.sampleTree_eval hF] at hc
  let v := compileDeclaredRootShift C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi
    (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1) (η/Real.sqrt 2)
    (C.sampleDrift r η hs.1 hs.2.2.1 hs.2.2.2.1)
  have hpr := sampleCorrelation_properties hs.2.2.1 hs.2.2.2.1
  have hp := sampleParent_squared hF x hs.1.le hlr (by linarith [hpr.1]) hpr.2.1 hpr.2.2
    (C.n+1) C.N (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1)
    (probabilityEndpoint_time _ _ C.h_pos _ (by omega)) E v hLf Lg.coe_nonneg (mul_pos hs.2.2.1 ha)
    hgl.continuous.measurable hfl
    (fun z z' => by simpa only [dist_eq_norm] using hgl.dist_le_mul z z') hc hnumi hnum
  unfold sampleFrom
  rw [dite_eq_left ⟨hs.1,hs.2.2.1,hs.2.2.2.1⟩]
  apply hp.mono
  have hh := mul_le_mul_of_nonneg_left (anchorGauge_circuitD_moment hd F x)
    (show 0 ≤ 40*(η*a)^2 by positivity)
  calc
    _ ≤ 40*(η*a)^2*(10*(circuitD F x)^2)+4*((circuitD F x)^2*en^2) := add_le_add hh le_rfl
    _ = _ := by ring
end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree

variable (C : CircuitParameters) {d : ℕ}

def depthBound : ℕ := 4*(C.N+1)^2

lemma meanTree_depth (hN : C.Nc≤C.N) (r σ : ℝ) :
    depth (C.meanTree (d:=d) r σ)≤C.depthBound := by
  exact meanCircuit_fixed_depth r C.T C.h C.ψ (σ/2) C.n C.m C.N C.nc C.Nc hN C.meanEndpoint _ _ _ _ _ _

lemma sampleTree_depth (r η : ℝ) (hη : 0<η) (hη1 : η≤1) :
    depth (C.sampleTree (d:=d) r η hη hη1)≤C.depthBound := by
  have hh := depth_forward r (sampleCorrelation η) C.h (C.n+1) C.N
    (anchor (Prod.fst : SampleInput d → Point d) (by fun_prop))
    (anchor Prod.snd (by fun_prop)) (C.sampleEndpoint η hη hη1) (b:=0) (by simp) (by simp)
  dsimp only [sampleTree,literalSample] at ⊢
  rw [depth_scale]
  unfold depthBound
  nlinarith

lemma depthBound_pos : 0<C.depthBound := by unfold depthBound; positivity
end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory MeanTree
open scoped Classical NNReal

variable {d : ℕ}

lemma ReservedProgram.full_fixedSeed_lip (S : ReservedProgram d) (F : Point d → ℝ) (K : ℝ)
    (h : ∀x y g, ‖S.pre.run F (x,g)-S.pre.run F (y,g)‖≤K*‖x-y‖) :
    ∀x y g, ‖S.full.program.run F (x,g)-S.full.program.run F (y,g)‖≤K*‖x-y‖ := by
  intro x y g
  rw [full_run S F x g,full_run S F y g,add_sub_add_right_eq_sub]
  exact h x y _

namespace CircuitParameters
variable (C : CircuitParameters)

lemma sampleFrom_lipschitz {F : Point d → ℝ} {lam : ℝ≥0} {q Kf Ki ef ei r η : ℝ}
    (hs : SampleSize lam q r η) (hRη : Real.sqrt (1-C.T^2)≤η) (hD : 0<C.D)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0≤Kf) (hKi : 0≤Ki)
    (hsmall : (lam:ℝ)*Ki*C.sampleCenterBudget r≤1)
    (Mf Mi : ℝ → ℝ → SeedProgram d)
    (hf : MeanCorrect F lam ((1+4*C.Af)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi) :
    ∀x y g, ‖(C.sampleFrom Mf Mi r η).pre.run F (x,g)-
      (C.sampleFrom Mf Mi r η).pre.run F (y,g)‖≤
      (lam:ℝ)*r*(C.Af*(depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ)*Kf)*‖x-y‖ := by
  let P : Bool → ℝ → ℝ → Prop := fun s => if s then
    MeanSize lam ((1+4*C.Af)*q) else MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2)))
  let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
  have hv := C.sampleTree_valid (d:=d) lam.coe_nonneg hs C.residual_pos hRη hD hA hAf
  have hrdy := hv.shiftReady (P true) (P false) (fun _ _ h => h.1.ne')
    (fun _ _ h => h.1.ne') _ _
  have hE := C.sampleCompiled_variation hs.1 hs.2.2.1 hs.2.2.2.1 hA hAf
    (mul_nonneg lam.coe_nonneg hKf) (mul_nonneg lam.coe_nonneg hKi) hsmall F P M hf.lip hi.lip
    (η/Real.sqrt 2) hrdy
  unfold sampleFrom
  rw [dite_eq_left ⟨hs.1,hs.2.2.1,hs.2.2.2.1⟩]
  dsimp only
  intro x y g
  have he := sampleParent_lipschitz F _ _ _ _ _ hE x y g
  convert! he using 1
  unfold sampleFinalBudget
  ring

lemma meanFrom_lipschitz {F : Point d → ℝ} {lam : ℝ≥0}
    {q Kf Ki Ks ef ei es ηmin r σ : ℝ}
    (hs : MeanSize lam q r σ) (hD : 0<C.D) (hψ : 0≤C.ψ)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0≤Kf) (hKi : 0≤Ki) (hKs : 0≤Ks)
    (hsmall : (lam:ℝ)*Ki*C.meanCenterBudget r σ≤1)
    (hRT : Real.sqrt (1-C.T^2)≤C.T)
    (hη : ηmin≤Real.sqrt (1-C.T^2)/C.T)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (S : ℝ → ℝ → ReservedProgram d)
    (hf : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (hS : SampleCorrect F lam (q/Real.sqrt (1-C.T^2)) Ks es ηmin S) :
    ∀x y g, ‖(C.meanFrom Mf Mi S r σ).program.run F (x,g)-
      (C.meanFrom Mf Mi S r σ).program.run F (y,g)‖≤
      (lam:ℝ)*(C.Af*(depth (C.meanTree (d:=d) r σ):ℝ)*Kf*(1+q*Ks))*‖x-y‖ := by
  let P : Bool → ℝ → ℝ → Prop := fun s => if s then
    MeanSize lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) else
    MeanSize lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2)))
  let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
  have hv := C.meanTree_valid (d:=d) lam.coe_nonneg hs hD hψ hA hAf
  have hrdy := hv.shiftReady (P true) (P false) (fun _ _ h => h.1.ne')
    (fun _ _ h => h.1.ne') _ _
  have hE := C.meanCompiled_variation hs.1 hs.2.2.1 hψ hA hAf
    (mul_nonneg lam.coe_nonneg hKf) (mul_nonneg lam.coe_nonneg hKi) hsmall F P M hf.lip hi.lip
    (Real.sqrt 3*σ/2) hrdy
  have ha := C.mean_anchor_size lam.coe_nonneg hs hRT
  have hSl := ReservedProgram.full_fixedSeed_lip _ F ((lam:ℝ)*r*Ks) (hS.lip _ _ ha hη)
  have hAf0 : 0<C.Af := hAf ▸ C.actualAf_pos
  have hT : 0≤C.T := by linarith [C.T_lower]
  have hK : 0≤C.Af*((lam:ℝ)*Kf)*(depth (C.meanTree (d:=d) r σ):ℝ) := by positivity
  unfold meanFrom
  rw [dite_eq_left hs.1]
  dsimp only
  intro x y g
  have he := meanParent_lipschitz F _ _ _ _ _ _ _ _ (mul_nonneg hK hs.1.le) hT hSl hE.1 hE.2 x y g
  apply he.trans
  have hq := mul_le_mul_of_nonneg_right hs.2.2.2.1 hKs
  have hTq : C.T*((lam:ℝ)*r^2*Ks)≤q*Ks :=
    (mul_le_of_le_one_left (show 0≤(lam:ℝ)*r^2*Ks by positivity) C.T_upper.le).trans hq
  have hh := mul_le_mul_of_nonneg_left hTq hK
  have heq : C.Af*((lam:ℝ)*Kf)*(depth (C.meanTree (d:=d) r σ):ℝ)+
      C.Af*((lam:ℝ)*Kf)*(depth (C.meanTree (d:=d) r σ):ℝ)*r*C.T*((lam:ℝ)*r*Ks)≤
      (lam:ℝ)*(C.Af*(depth (C.meanTree (d:=d) r σ):ℝ)*Kf*(1+q*Ks)) := by nlinarith
  exact mul_le_mul_of_nonneg_right heq (norm_nonneg _)

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree Coupling
open scoped Classical NNReal

lemma mean_error_envelope {u k σ T es a en D M : ℝ}
    (hu : 0≤u) (hk : 0≤k) (_hσ : 0≤σ) (hT : 0≤T) (hT1 : T≤1)
    (hes : 0≤es) (ha : 0≤a) (hen : 0≤en) (hM : 1≤M) (hub : u≤σ*k) :
    2*u^2*(T^2*(es^2*D^2))+80*(σ*a)^2*(M*D^2)+8*(σ/2*D)^2*en^2≤
      σ^2*(2*k*es+10*M*a+2*en)^2*D^2 := by
  have hut : u*T≤σ*k := (mul_le_of_le_one_right hu hT1).trans hub
  have hv := pow_le_pow_left₀ (mul_nonneg hu hT) hut 2
  have hv' := mul_le_mul_of_nonneg_right hv (show 0≤2*es^2 by positivity)
  have hm : 80*M≤100*M^2 := by nlinarith
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg (σ*a))
  have h₁ : 0≤(2*k*es)*(10*M*a) := by positivity
  have h₂ : 0≤(2*k*es)*(2*en) := by positivity
  have h₃ : 0≤(10*M*a)*(2*en) := by positivity
  have hsum : 2*u^2*T^2*es^2+80*(σ*a)^2*M+2*σ^2*en^2≤
      σ^2*(2*k*es+10*M*a+2*en)^2 := by
    have hx := mul_nonneg (sq_nonneg σ) h₁
    have hy := mul_nonneg (sq_nonneg σ) h₂
    have hz := mul_nonneg (sq_nonneg σ) h₃
    nlinarith [sq_nonneg (σ*k*es),sq_nonneg (σ*en)]
  have hres := mul_le_mul_of_nonneg_right hsum (sq_nonneg D)
  nlinarith only [hres]

lemma sample_error_envelope {η a en D : ℝ} (hη : 0≤η) (hη1 : η≤1)
    (ha : 0≤a) (hen : 0≤en) :
    (400*(η*a)^2+4*en^2)*D^2≤(20*a+2*en)^2*D^2 := by
  have hη2 : η^2≤1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hη2 (sq_nonneg a)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg D)
  nlinarith [mul_nonneg ha hen]

namespace CircuitParameters
variable (C : CircuitParameters) {d : ℕ}

def compilerError (H Kf q ei ef : ℝ) : ℝ :=
  2*(1+2*H)*(C.Af*Kf*q*ei+ef)

def meanError (H Kf q es ei ef en : ℝ) : ℝ :=
  2*(C.Af*Kf*H*q)*es+10*(20+16*circuitGrowthConstant^2)*C.compilerError H Kf q ei ef+2*en

def sampleError (H Kf q ei ef en : ℝ) : ℝ :=
  20*C.compilerError H Kf q ei ef+2*en

lemma physical_mean_factor {lam q Kf r σ H : ℝ}
    (hs : MeanSize lam q r σ) (hlam : 0≤lam) (hAf : 0≤C.Af) (hK : 0≤Kf)
    (hH : (depth (C.meanTree (d:=d) r σ):ℝ)≤H) :
    C.Af*(lam*Kf)*(depth (C.meanTree (d:=d) r σ):ℝ)*r≤σ*(C.Af*Kf*H*q) := by
  have hq := hs.nonneg hlam
  have h₁ := mul_le_mul_of_nonneg_left hs.2.2.2.2
    (show 0≤C.Af*Kf*(depth (C.meanTree (d:=d) r σ):ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hH (show 0≤σ*C.Af*Kf*q by positivity [hs.2.2.1])
  nlinarith

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree Coupling MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable {d : ℕ}

namespace CircuitParameters
variable (C : CircuitParameters)

lemma meanCenter_scaled {lam q r σ : ℝ} (hs : MeanSize lam q r σ)
    (_hlam : 0≤lam) (hA : 0≤C.A) : lam*C.meanCenterBudget r σ≤2*C.A*q := by
  have hh : lam*r/σ≤q := (div_le_iff₀ hs.2.2.1).mpr hs.2.2.2.2
  have he : lam*(r/σ+r^2)≤2*q := by rw [mul_add,←mul_div_assoc]; linarith [hs.2.2.2.1]
  have hh := mul_le_mul_of_nonneg_left he hA
  unfold meanCenterBudget
  nlinarith only [hh]

lemma sampleCenter_scaled {lam q r η : ℝ} (hs : SampleSize lam q r η)
    (hlam : 0≤lam) (hA : 0≤C.A) : lam*C.sampleCenterBudget r≤2*C.A*q := by
  have hq := hs.nonneg hlam
  have he := hs.2.2.2.2.trans (mul_le_of_le_one_right hq hs.2.2.2.1)
  unfold sampleCenterBudget
  nlinarith [mul_le_mul_of_nonneg_left he hA,mul_nonneg hA hq]

lemma physical_small_of_scaled {lam B A q K : ℝ} (_hA : 0≤A) (_hq : 0≤q) (hK : 0≤K)
    (hB : 0≤lam*B) (hscale : lam*B≤2*A*q)
    (hp : 2*A*q*(2*Real.pi+2)≤1) (hcon : 4*A*q*K≤1) :
    lam*B*(2*Real.pi+2)≤1 ∧ 4*B^2*(lam*K)^2≤1 ∧ lam*K*B≤1 := by
  have hs := mul_le_mul_of_nonneg_right hscale (show 0≤2*Real.pi+2 by positivity [Real.pi_pos])
  have hk := mul_le_mul_of_nonneg_right hscale hK
  have hg : 0≤lam*B*K := mul_nonneg hB hK
  have hu : lam*B*K≤1/2 := by linarith
  refine ⟨hs.trans hp,?_,by nlinarith⟩
  have hh := pow_le_pow_left₀ hg hu 2
  nlinarith only [hh]

def MeanNumericalReady {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (q en : ℝ) (hq : q≤1/4) : Prop :=
  ∀x r σ,∀hs : MeanSize lam q r σ,
    CalibratedMeanCircuit (r:=r) (T:=C.T) (h:=C.h) (ψ:=C.ψ) (s:=σ/2)
      hF x hs.1 (by linarith [hs.2.2.2.1] : (lam:ℝ)*r^2≤1/2)
      (by linarith [C.T_lower]) C.T_upper C.h_pos C.n C.N (en^2)

def SampleNumericalReady {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (q en : ℝ) : Prop :=
  ∀x r η,∀hs : SampleSize lam q r η,∀hl : (lam:ℝ)*r^2≤1/2,
    Integrable (fun Y => ‖sampleMeanCircuit F x r (sampleCorrelation η) C.h
      (C.n+1) C.N (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1) Y-
      (sampleCorrelation η)⁻¹ • fullProbabilityFlow hF x hs.1.le hl (sampleCorrelation η) Y‖^2)
      (stdGaussian (Point d)) ∧
    (∫Y,‖sampleMeanCircuit F x r (sampleCorrelation η) C.h
      (C.n+1) C.N (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1) Y-
      (sampleCorrelation η)⁻¹ • fullProbabilityFlow hF x hs.1.le hl (sampleCorrelation η) Y‖^2
      ∂stdGaussian (Point d))≤(circuitD F x)^2*en^2

lemma compilerError_mono {H H' Kf q ei ef : ℝ} (hHH : H≤H')
    (hAf : 0≤C.Af) (hK : 0≤Kf) (hq : 0≤q) (hei : 0≤ei) (hef : 0≤ef) :
    C.compilerError H Kf q ei ef≤C.compilerError H' Kf q ei ef := by
  unfold compilerError
  nlinarith [mul_nonneg (sub_nonneg.mpr hHH) (show 0≤C.Af*Kf*q*ei+ef by positivity)]

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree Coupling MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

theorem meanFrom_correct {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki Ks ef ei es en ηmin : ℝ} (hd : 1≤d) (hlam : (lam:ℝ)≤1)
    (hq : 0≤q) (hql : q≤1/4) (hRT : Real.sqrt (1-C.T^2)≤C.T)
    (hη : ηmin≤Real.sqrt (1-C.T^2)/C.T)
    (hD : 1≤C.D) (hψ : 0≤C.ψ) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0≤Kf) (hKi : 0≤Ki) (hKs : 0≤Ks)
    (hef : 0<ef) (hei : 0≤ei) (hes : 0≤es) (hen : 0≤en)
    (hsmall : 2*C.A*q*(2*Real.pi+2)≤1) (hcon : 4*C.A*q*Ki≤1) (hqs : q*Ks≤1)
    (hm : C.m=C.n) (hnc : C.nc=C.n) (hNc : C.Nc=C.N)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (S : ℝ → ℝ → ReservedProgram d)
    (B : ℕ) (hBD : (B:ℝ)≤C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (hS : SampleCorrect F lam (q/Real.sqrt (1-C.T^2)) Ks es ηmin S)
    (hrsv : ∀r,(S r (Real.sqrt (1-C.T^2)/C.T)).reserve=(Real.sqrt (1-C.T^2)/C.T)/2)
    (hnum : C.MeanNumericalReady hF q en hql) :
    MeanCorrect F lam q (2*C.Af*C.depthBound*Kf)
      (C.meanError C.depthBound Kf q es ei ef en) (C.meanFrom Mf Mi S) := by
  have hA0 : 0<C.A := hA ▸ C.actualA_pos
  have hAf0 : 0<C.Af := hAf ▸ C.actualAf_pos
  have hH : 0≤(C.depthBound:ℝ) := Nat.cast_nonneg _
  have small {r σ : ℝ} (hs : MeanSize lam q r σ) :=
    physical_small_of_scaled hA0.le hq hKi
      (show 0≤(lam:ℝ)*C.meanCenterBudget r σ by unfold meanCenterBudget; positivity [hs.1,hs.2.2.1])
      (C.meanCenter_scaled hs lam.coe_nonneg hA0.le) hsmall hcon
  constructor
  · intro r σ hs x y g
    have he := C.meanFrom_lipschitz hs (by linarith) hψ hA hAf hKf hKi hKs
      (small hs).2.2 hRT hη Mf Mi S hf hi hS x y g
    have hdep : (depth (C.meanTree (d:=d) r σ):ℝ)≤C.depthBound :=
      by exact_mod_cast C.meanTree_depth (d:=d) hNc.le r σ
    have hdep0 : 0≤(depth (C.meanTree (d:=d) r σ):ℝ) := Nat.cast_nonneg _
    have hh : (depth (C.meanTree (d:=d) r σ):ℝ)*(1+q*Ks)≤2*C.depthBound := by
      have ht := mul_le_mul_of_nonneg_left hqs hdep0
      nlinarith
    have hk := mul_le_mul_of_nonneg_right hh
      (show 0≤(lam:ℝ)*C.Af*Kf*‖x-y‖ by positivity)
    apply he.trans
    nlinarith only [hk]
  · intro r σ hs x
    have hL : (lam:ℝ)*r≤1 := (mul_le_of_le_one_left hs.1.le hlam).trans hs.2.1
    have hp := C.meanFrom_squared hF hd hs hql hL hD hψ hA hAf hKf hKi hef hei
      (small hs).1 (small hs).2.1 hRT hη hm hnc hNc Mf Mi S B hBD hbudget hf hi hS
      (hrsv r) x (hnum x r σ hs)
    apply hp.mono
    let dep := (depth (C.meanTree (d:=d) r σ):ℝ)
    let a := C.compilerError dep Kf q ei ef
    let k := C.Af*Kf*C.depthBound*q
    have hdep : dep≤C.depthBound := by dsimp only [dep]; exact_mod_cast C.meanTree_depth (d:=d) hNc.le r σ
    have hdep0 : 0≤dep := by dsimp [dep]; positivity
    have ha : 0≤a := by dsimp [a,compilerError]; positivity
    have ha' : a≤C.compilerError C.depthBound Kf q ei ef := C.compilerError_mono hdep hAf0.le hKf hq hei hef.le
    have hu := C.physical_mean_factor hs lam.coe_nonneg hAf0.le hKf hdep
    have he := mean_error_envelope (D:=circuitD F x)
      (show 0≤C.Af*((lam:ℝ)*Kf)*dep*r by positivity [hs.1])
      (show 0≤k by dsimp [k]; positivity) hs.2.2.1.le
      (by linarith [C.T_lower] : 0≤C.T) C.T_upper.le hes ha hen
      (show 1≤20+16*circuitGrowthConstant^2 by nlinarith [sq_nonneg circuitGrowthConstant]) hu
    apply he.trans
    have hem : 2*k*es+10*(20+16*circuitGrowthConstant^2)*a+2*en≤
        C.meanError C.depthBound Kf q es ei ef en := by
      unfold meanError
      have hh := mul_le_mul_of_nonneg_left ha' (show 0≤10*(20+16*circuitGrowthConstant^2) by positivity)
      exact add_le_add (add_le_add le_rfl hh) le_rfl
    have he0 : 0≤2*k*es+10*(20+16*circuitGrowthConstant^2)*a+2*en := by dsimp [k]; positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he0 hem 2) (sq_nonneg σ)) (sq_nonneg _)
end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
