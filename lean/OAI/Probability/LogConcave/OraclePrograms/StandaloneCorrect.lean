import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.Shape
import OAI.Probability.LogConcave.OraclePrograms.SampleCorrect

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter MeanTree MeasureTheory ProbabilityTheory
open scoped Classical NNReal Topology

variable {d : ℕ}

def StandaloneCorrect (F : Point d → ℝ) (lam q K e ηmin : ℝ) :
    {k : RoutineKind} → RoutineValue d k → Prop
  | .mean,M => MeanCorrect F lam q K e M
  | .sample,S => SampleCorrect F lam q K e ηmin S

def UniformAccuracy (κ t w : ℝ) (_ : ℝ) (n N : ℕ) (ht : 0 < t) (hts : t≤1/44)
    (L : RoutineLabel) : Prop :=
  ∀q : ℕ → ℝ,LogPowerRate q (κ*L.b) → (∀ᶠ d : ℕ in atTop,0 < q d) →
  ∃K : ℝ,0 ≤ K ∧ ∃e : ℕ → ℝ,LogPowerRate e (κ*L.p) ∧
    (∀ᶠ d : ℕ in atTop,0 < e d) ∧
    ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,SourceShape κ t w n N d C →
      ∀{F : Point d → ℝ} {lam : ℝ≥0},∀_ : Primitive F lam,0 < lam → (lam:ℝ)≤1 →
      StandaloneCorrect F lam (q d) K (e d) ((d:ℝ)^(-(κ*t))) (constructRoutine d C ht hts L)

lemma sourceA_pos (κ t w : ℝ) (n d : ℕ) : 0 < sourceA κ t w n d := by
  have hB := (fixedCenteringBudget_spec n).1
  have hP := (fixedProbabilityBudget_spec n).1
  unfold sourceA
  positivity

lemma childSizes_positive {κ t w : ℝ} (n : ℕ) {q : ℕ → ℝ}
    (hq : ∀ᶠ d : ℕ in atTop,0 < q d) :
    (∀ᶠ d : ℕ in atTop,0 < meanFinalSize κ t n q d) ∧
    (∀ᶠ d : ℕ in atTop,0 < sampleFinalSize n q d) ∧
    (∀ᶠ d : ℕ in atTop,0 < internalSize κ t w n q d) ∧
    (∀ᶠ d : ℕ in atTop,0 < anchorSize κ t q d) := by
  have h : ∀ᶠ d : ℕ in atTop,0 < meanFinalSize κ t n q d ∧ 0 < sampleFinalSize n q d ∧
      0 < internalSize κ t w n q d ∧ 0 < anchorSize κ t q d := by
    filter_upwards [hq,eventually_ge_atTop (1:ℕ)] with d hd hd1
    have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
    have hAf := sourceAf_pos n
    have hA := sourceA_pos κ t w n d
    unfold meanFinalSize sampleFinalSize internalSize anchorSize
    exact ⟨by positivity,by positivity,by positivity,by positivity⟩
  exact ⟨h.mono (fun _ h => h.1),h.mono (fun _ h => h.2.1),h.mono (fun _ h => h.2.2.1),h.mono (fun _ h => h.2.2.2)⟩

lemma uniformAccuracy_terminal {κ t w J K₀ : ℝ} {n N : ℕ} (hκ : 0 < κ)
    (ht : 0 < t) (hts : t≤1/44) (L : RoutineLabel) (hL : L.Admissible t K₀)
    (hterm : L.terminal) : UniformAccuracy κ t w J n N ht hts L := by
  intro q hq hqpos
  have hb := hL.b_lower ht.le
  have hqsmall := hq.eventually_lt_const (show 0 < κ*L.b by positivity [hb])
    (by norm_num : (0:ℝ)<1/2)
  cases L with | mk kind b p =>
    cases kind with
    | mean =>
      let c := 4*(Real.pi+2)
      have hc : 0 < c := by dsimp [c]; positivity [Real.pi_pos]
      refine ⟨1,by norm_num,(fun d => c*q d),(hq.const_mul c).mono (by dsimp [RoutineLabel.terminal] at hterm; nlinarith),?_,?_⟩
      · exact hqpos.mono (fun _ h => mul_pos hc h)
      · filter_upwards [hqsmall] with d hd C hC F lam hF hlam hlam1
        rw [constructRoutine,dite_eq_left hterm]
        exact terminalMean_correct hF ((le_abs_self _).trans hd.le)
    | sample =>
      let c := 2*terminalTransportConstant*(Real.pi+3)
      have hc : 0 < c := by dsimp [c]; positivity [terminalTransportConstant_pos,Real.pi_pos]
      refine ⟨1,by norm_num,(fun d => c*q d),(hq.const_mul c).mono (by dsimp [RoutineLabel.terminal] at hterm; nlinarith),?_,?_⟩
      · exact hqpos.mono (fun _ h => mul_pos hc h)
      · filter_upwards [hqsmall] with d hd C hC F lam hF hlam hlam1
        rw [constructRoutine,dite_eq_left hterm]
        exact terminalSample_correct hF ((le_abs_self _).trans hd.le) _

theorem uniform_routine_accuracy {κ t w J K₀ : ℝ} {n N : ℕ}
    (hκ : 0 < κ) (ht : 0 < t) (hts : t<1/100) (hw : 0 < w) (hwt : w<t)
    (hJK : K₀≤J) (_ : N=numericalLayerCount J)
    (hbudget : ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,SourceShape κ t w n N d C →
      ∃B : ℕ,(B:ℝ)≤C.D ∧ ∀L : RoutineLabel,L.Admissible t K₀ →
      RoutineBudget B (Real.sqrt (1-C.T^2)/C.T) 1 (constructRoutine d C ht (by linarith) L))
    (hnum : ∀q : ℕ → ℝ,LogPowerRate q (κ*(1/2)) →
      ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,SourceShape κ t w n N d C →
      ∀{F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,0 < lam → (lam:ℝ)≤1 →
      ∀hql : q d≤1/4,C.MeanNumericalReady hF (q d) ((d:ℝ)^(-(κ*J))) hql ∧
      C.SampleNumericalReady hF (q d) ((d:ℝ)^(-(κ*J)))) :
    ∀L : RoutineLabel,L.Admissible t K₀ → UniformAccuracy κ t w J n N ht (by linarith) L := by
  let hts' : t≤1/44 := by linarith
  apply routine_induction ht hts'
  · intro L hterm hL
    exact uniformAccuracy_terminal hκ ht hts' L hL hterm
  · intro L hnt ih hL q hq hqpos
    have hb := hL.b_lower ht.le
    have hpJ : L.p≤J := hL.2.1.trans hJK
    have hqp := childSizes_positive (κ:=κ) (t:=t) (w:=w) n hqpos
    have hqi := internalSize_rate hκ ht hw hwt n hq
    have hqnum := hnum q (hq.mono (by nlinarith))
    have hsmall := (small_coefficient_rate hκ ht hw hwt hts hb n hq).eventually_lt_const
      (by positivity : 0 < κ/3) (by positivity : (0:ℝ)<1/(2*(2*Real.pi+2)))
    have hqsmall := hq.eventually_lt_const (show 0 < κ*L.b by positivity [hb])
      (by norm_num : (0:ℝ)<1/4)
    have hgeom := sourceCorrelation_eventually (mul_pos hκ ht)
    have hanchor := source_anchor_radius (mul_pos hκ ht)
    let H : ℝ := (4*(N+1)^2:ℕ)
    have hH : 0 ≤ H := Nat.cast_nonneg _
    have hAf : 0 < sourceAf n := sourceAf_pos n
    cases L with | mk kind b p =>
      cases kind with
      | mean =>
        have hLF := RoutineStep.meanFinal (t:=t) b p
        have hLI := RoutineStep.internal (t:=t) RoutineKind.mean RoutineKind.mean b p
        have hLS := RoutineStep.internal (t:=t) RoutineKind.mean RoutineKind.sample b p
        have hAF := hL.child ht.le hnt hLF
        have hAI := hL.child ht.le hnt hLI
        have hAS := hL.child ht.le hnt hLS
        obtain ⟨Kf,hKf,ef,hef,hefpos,hf⟩ := ih _ hLF hAF (meanFinalSize κ t n q) (meanFinalSize_rate n hq) hqp.1
        obtain ⟨Ki,hKi,ei,hei,heipos,hi⟩ := ih _ hLI hAI (internalSize κ t w n q) hqi hqp.2.2.1
        obtain ⟨Ks,hKs,es,hes,hespos,hS⟩ := ih _ hLS hAS (anchorSize κ t q) (anchorSize_rate hκ.le ht.le hq) hqp.2.2.2
        let e := fun d => 2*(sourceAf n*Kf*H*q d)*es d+
          10*(20+16*circuitGrowthConstant^2)*(2*(1+2*H)*(sourceAf n*Kf*q d*ei d+ef d))+
          2*(d:ℝ)^(-(κ*J))
        have he : LogPowerRate e (κ*p) := by
          apply (meanError_rate hκ.le hb hpJ (sourceAf n) H Kf hq hes hei hef).congr
          filter_upwards [] with d
          dsimp only [e]
          ring
        have hepos : ∀ᶠ d : ℕ in atTop,0 < e d := by
          filter_upwards [hqpos,hefpos,heipos,hespos,eventually_ge_atTop (1:ℕ)] with d hqd hfd hid hsd hd1
          have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
          dsimp [e]
          positivity
        refine ⟨2*sourceAf n*H*Kf,by positivity,e,he,hepos,?_⟩
        have hcon := ((small_coefficient_rate hκ ht hw hwt hts hb n hq).const_mul (4*Ki)).eventually_lt_const
          (by positivity : 0 < κ/3) (by norm_num : (0:ℝ)<1)
        have hqs := (hq.mul_const Ks).eventually_lt_const (show 0 < κ*b by positivity [hb]) (by norm_num : (0:ℝ)<1)
        filter_upwards [hf,hi,hS,hbudget,hqnum,hqpos,hefpos,heipos,hespos,hsmall,hcon,hqs,hqsmall,hgeom,hanchor,
          eventually_ge_atTop (1:ℕ)] with d hfd hid hsd hbd hnd hqd hef0 hei0 hes0 hsm hco hqsd hql hdgeom hdanchor hd1
        intro C hC F lam hF hlam hlam1
        have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
        have hR : Real.sqrt (1-C.T^2)=(d:ℝ)^(-(κ*t)) := by
          rw [hC.T_eq,←hdgeom.2.2,Real.sqrt_sq (Real.rpow_pos_of_pos hd0 _).le]
        have hRT : Real.sqrt (1-C.T^2)≤C.T := by
          apply (div_le_one (by linarith [C.T_lower] : 0 < C.T)).mp
          rw [hC.T_eq]
          exact hdanchor.2
        have hη : (d:ℝ)^(-(κ*t))≤Real.sqrt (1-C.T^2)/C.T := by rw [hC.T_eq]; exact hdanchor.1
        have hD : 1≤C.D := by rw [hC.D_eq]; exact Real.one_le_rpow (by exact_mod_cast hd1) (mul_pos hκ ht).le
        have hψ : 0 ≤ C.ψ := by rw [hC.ψ_eq]; positivity
        obtain ⟨B,hBD,hbud⟩ := hbd C hC
        have hB : (B:ℝ)≤C.D^2 := hBD.trans (by nlinarith)
        have hsmall' : 2*C.A*q d*(2*Real.pi+2)≤1 := by
          rw [hC.A]
          have hh := (le_abs_self _).trans hsm.le
          have hp : 0 < 2*(2*Real.pi+2) := by positivity [Real.pi_pos]
          have he := (le_div_iff₀ hp).mp hh
          nlinarith only [he]
        have hcon' : 4*C.A*q d*Ki≤1 := by
          rw [hC.A]
          have he := (le_abs_self _).trans hco.le
          nlinarith only [he]
        have hnmc : C.m=C.n := hC.m_eq.trans hC.n_eq.symm
        have hncc : C.nc=C.n := hC.nc_eq.trans hC.n_eq.symm
        have hNcc : C.Nc=C.N := hC.Nc_eq.trans hC.N_eq.symm
        have hqle : q d≤1/4 := (le_abs_self _).trans hql.le
        have hfc := hfd C hC hF hlam hlam1
        have hic := hid C hC hF hlam hlam1
        have hsc := hsd C hC hF hlam hlam1
        have hf' : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q d) Kf (ef d)
            (constructRoutine d C ht hts' ⟨.mean,b+t,p⟩) := by
          simpa only [StandaloneCorrect,meanFinalSize,hC.Af,hR] using hfc
        have hi' : MeanCorrect F lam (q d*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki (ei d)
            (constructRoutine d C ht hts' ⟨.mean,b-10*t,p-1/4⟩) := by
          simpa only [StandaloneCorrect,internalSize,hC.D_eq,hC.A,hR] using hic
        have hs' : SampleCorrect F lam (q d/Real.sqrt (1-C.T^2)) Ks (es d) ((d:ℝ)^(-(κ*t)))
            (constructRoutine d C ht hts' ⟨.sample,b-10*t,p-1/4⟩) := by
          simpa only [StandaloneCorrect,anchorSize,hR] using hsc
        have hp := C.meanFrom_correct hF hd1 hlam1 hqd.le hqle hRT hη hD hψ hC.A_eq hC.Af_eq
          hKf hKi hKs hef0 hei0.le hes0.le (Real.rpow_pos_of_pos hd0 _).le hsmall' hcon'
          ((le_abs_self _).trans hqsd.le) hnmc hncc hNcc _ _ _ B hB
          (fun s r τ => by cases s; exact hbud _ hAI r τ; exact hbud _ hAF r τ)
          hf' hi' hs' (fun r => (hbud _ hAS r _ (Or.inl rfl)).reserve)
          (hnd C hC hF hlam hlam1 hqle).1
        rw [constructRoutine,dite_eq_right hnt]
        simpa only [StandaloneCorrect,hC.Af,hC.depth,CircuitParameters.meanError,
          CircuitParameters.compilerError,e,H] using hp
      | sample =>
        have hLF := RoutineStep.sampleFinal (t:=t) b p
        have hLI := RoutineStep.internal (t:=t) RoutineKind.sample RoutineKind.mean b p
        have hAF := hL.child ht.le hnt hLF
        have hAI := hL.child ht.le hnt hLI
        obtain ⟨Kf,hKf,ef,hef,hefpos,hf⟩ := ih _ hLF hAF (sampleFinalSize n q) (sampleFinalSize_rate n hq) hqp.2.1
        obtain ⟨Ki,hKi,ei,hei,heipos,hi⟩ := ih _ hLI hAI (internalSize κ t w n q) hqi hqp.2.2.1
        let e := fun d => 20*(2*(1+2*H)*(sourceAf n*Kf*q d*ei d+ef d))+2*(d:ℝ)^(-(κ*J))
        have he : LogPowerRate e (κ*p) := sampleError_rate hκ.le hb hpJ (sourceAf n) H Kf hq hei hef
        have hepos : ∀ᶠ d : ℕ in atTop,0 < e d := by
          filter_upwards [hqpos,hefpos,heipos,eventually_ge_atTop (1:ℕ)] with d hqd hfd hid hd1
          have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
          dsimp [e]
          positivity
        refine ⟨sourceAf n*H*Kf,by positivity,e,he,hepos,?_⟩
        have hcon := ((small_coefficient_rate hκ ht hw hwt hts hb n hq).const_mul (4*Ki)).eventually_lt_const
          (by positivity : 0 < κ/3) (by norm_num : (0:ℝ)<1)
        filter_upwards [hf,hi,hbudget,hqnum,hqpos,hefpos,heipos,hsmall,hcon,hqsmall,hgeom,
          eventually_ge_atTop (1:ℕ)] with d hfd hid hbd hnd hqd hef0 hei0 hsm hco hql hdgeom hd1
        intro C hC F lam hF hlam hlam1
        have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
        have hR : Real.sqrt (1-C.T^2)=(d:ℝ)^(-(κ*t)) := by
          rw [hC.T_eq,←hdgeom.2.2,Real.sqrt_sq (Real.rpow_pos_of_pos hd0 _).le]
        have hD : 1≤C.D := by rw [hC.D_eq]; exact Real.one_le_rpow (by exact_mod_cast hd1) (mul_pos hκ ht).le
        obtain ⟨B,hBD,hbud⟩ := hbd C hC
        have hB : (B:ℝ)≤C.D^2 := hBD.trans (by nlinarith)
        have hsmall' : 2*C.A*q d*(2*Real.pi+2)≤1 := by
          rw [hC.A]
          have hh := (le_abs_self _).trans hsm.le
          have hp : 0 < 2*(2*Real.pi+2) := by positivity [Real.pi_pos]
          have he := (le_div_iff₀ hp).mp hh
          nlinarith only [he]
        have hcon' : 4*C.A*q d*Ki≤1 := by
          rw [hC.A]
          have he := (le_abs_self _).trans hco.le
          nlinarith only [he]
        have hqle : q d≤1/4 := (le_abs_self _).trans hql.le
        have hf' : MeanCorrect F lam ((1+4*C.Af)*q d) Kf (ef d)
            (constructRoutine d C ht hts' ⟨.mean,b,p⟩) := by
          simpa only [StandaloneCorrect,sampleFinalSize,hC.Af] using hfd C hC hF hlam hlam1
        have hi' : MeanCorrect F lam (q d*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki (ei d)
            (constructRoutine d C ht hts' ⟨.mean,b-10*t,p-1/4⟩) := by
          simpa only [StandaloneCorrect,internalSize,hC.D_eq,hC.A,hR] using hid C hC hF hlam hlam1
        have hp := C.sampleFrom_correct hF hd1 hlam1 hqd.le hqle hR.le hD hC.A_eq hC.Af_eq
          hKf hKi hef0 hei0.le (Real.rpow_pos_of_pos hd0 _).le hsmall' hcon'
          _ _ B hB (fun s r τ => by cases s; exact hbud _ hAI r τ; exact hbud _ hAF r τ)
          hf' hi' (hnd C hC hF hlam hlam1 hqle).2
        rw [constructRoutine,dite_eq_right hnt]
        simpa only [StandaloneCorrect,hC.Af,hC.depth,CircuitParameters.sampleError,
          CircuitParameters.compilerError,e,H] using hp
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter MeasureTheory ProbabilityTheory
open scoped Classical NNReal

theorem calibrated_sample_circuit_order {κ J b w : ℝ} (hκ : 0<κ) (hJ : 1≤J)
    (hb : 1/2≤b) (hw : 0<w) (n : ℕ) (hn : 0<n)
    (hnw : J+10<w*((n:ℝ)-3)) :
      ∀{S : ℝ},0≤S → ∀ksize : ℕ,∀ᶠ d : ℕ in atTop,
      let h := (d:ℝ)^(-(κ*w))
      ∃_ : 0<h,∀{F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,∀x : Point d,
      ∀{r : ℝ},∀hr : 0<r,r≤1 → 0<lam → (lam:ℝ)*r≤1 →
      (lam:ℝ)*r^2≤S*dimensionLog d^ksize*(d:ℝ)^(-(κ*b)) →
      ∃hl : (lam:ℝ)*r^2≤1/2,∀{T : ℝ},1/2≤T → T<1 → ∀e : ProbabilityNode T h n,
      Integrable (fun z => ‖sampleMeanCircuit F x r T h n (numericalLayerCount J) e z-
        T⁻¹ • fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n e) z‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖sampleMeanCircuit F x r T h n (numericalLayerCount J) e z-
        T⁻¹ • fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n e) z‖^2 ∂stdGaussian (Point d))≤
        (circuitD F x)^2*(d:ℝ)^(-(2*κ*J)) := by
  obtain ⟨A,C,hC,k,hproducer⟩ := sampleMeanCircuit_rms n hn
  intro S hS ksize
  have hc := sampleScalarCalibration_uniform k n (numericalLayerCount J) ksize A C hS hκ hJ hb hw hnw
    (numericalLayerCount_bound J)
  have hhsmall := (LogPowerRate.power (κ*w)).eventually_lt_const (mul_pos hκ hw)
    (Real.log_pos (by norm_num : (1:ℝ)<2))
  filter_upwards [hc,hhsmall,eventually_ge_atTop (1:ℕ)] with d hd hdh hdim
  intro h
  have hdpos : (0:ℝ)<d := by exact_mod_cast hdim
  have hh : 0<h := Real.rpow_pos_of_pos hdpos _
  refine ⟨hh,?_⟩
  intro F lam hF x r hr hr1 hlam hL hl₀
  obtain ⟨hl,hq,he⟩ := hd lam r hr hl₀
  refine ⟨hl,?_⟩
  intro T hT hT1 e
  have hp := hproducer hF x hr hr1 hlam hl hL hdim hT hT1 hh
    ((le_abs_self _).trans hdh.le) hq (numericalLayerCount J) e
  exact ⟨hp.1,hp.2.trans (mul_le_mul_of_nonneg_left he (sq_nonneg _))⟩
end LogConcaveSampling

end

end

end OAI
