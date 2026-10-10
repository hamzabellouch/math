import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.RoutineBudget
import OAI.Probability.LogConcave.OraclePrograms.FullTape
import OAI.Probability.LogConcave.Complexity.OccurrenceBudget

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter Quadrature MeanTree
open scoped Topology Classical

lemma source_anchor_radius {a : ℝ} (ha : 0<a) :
    ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-a)≤Real.sqrt (1-(sourceCorrelation a d)^2)/(sourceCorrelation a d) ∧
      Real.sqrt (1-(sourceCorrelation a d)^2)/(sourceCorrelation a d)≤1 := by
  have he := sourceCorrelation_eventually ha
  have ht := (sourceCorrelation_tendsto ha).eventually (lt_mem_nhds (by norm_num : (3/4:ℝ)<1))
  filter_upwards [he,ht,eventually_ge_atTop (1:ℕ)] with d hd hT hd1
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
  have hR := Real.rpow_pos_of_pos hd0 (-a)
  have hr : Real.sqrt (1-(sourceCorrelation a d)^2)=(d:ℝ)^(-a) := by
    rw [←hd.2.2,Real.sqrt_sq hR.le]
  rw [hr]
  constructor
  · exact (le_div_iff₀ hd.1).mpr (by nlinarith [mul_le_mul_of_nonneg_left hd.2.1.le hR.le])
  · apply (div_le_one hd.1).mpr
    nlinarith [hd.2.2]

theorem literal_recursive_budget_order {t κ : ℝ} (ht : 0<t) (hs : t≤1/44) (hκ : 0<κ)
    (N Nc : ℕ) (L : RoutineLabel) : ∃w : ℝ,0<w ∧ w<t ∧
      ∀n m nc,∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,
        C.n=n → C.m=m → C.N=N → C.nc=nc → C.Nc=Nc →
        C.T=sourceCorrelation (κ*t) d → C.h=(d:ℝ)^(-(κ*w)) → C.D=(d:ℝ)^(κ*t) →
        ∀η₁ : ℝ,(d:ℝ)^(-(κ*t))≤η₁ → η₁≤1 →
        ∃B : ℕ,(B:ℝ)≤C.D ∧
          RoutineBudget B (Real.sqrt (1-C.T^2)/C.T) η₁ (constructRoutine d C ht hs L) := by
  obtain ⟨w,hw,hwt,hcost⟩ := exists_cost_mesh_exponent ht hκ N Nc (L.rank t)
  refine ⟨w,hw,hwt,?_⟩
  intro n m nc
  filter_upwards [hcost n m nc,source_anchor_radius (mul_pos hκ ht),eventually_ge_atTop (1:ℕ)] with d hd hanchor hd1
  intro C hn hm hN hnc hNc hT hh hD η₁ hηR hη1
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
  have hdge : (1:ℝ)≤d := by exact_mod_cast hd1
  have hDpos : 0<C.D := by rw [hD]; exact Real.rpow_pos_of_pos hd0 _
  have hDone : 1≤C.D := by rw [hD]; exact Real.one_le_rpow hdge (mul_pos hκ ht).le
  let c := sourceOccurrenceBudget (κ*t) (κ*w) n m N nc Nc d
  let B := 2*(40*c+40)^L.rank t
  have hcap : (B:ℝ)≤C.D := by simpa only [B,c,hD] using hd
  refine ⟨B,hcap,?_⟩
  apply constructRoutine_budget C ht hs c η₁ hDpos
  · intro r σ
    unfold CircuitParameters.meanTree
    rw [cost_literalMean]
    simp only [hn,hm,hN,hnc,hNc,hT,hh]
    unfold c sourceOccurrenceBudget
    omega
  · intro r η hη hηpos hηle
    unfold CircuitParameters.sampleTree
    have hradius : (d:ℝ)^(-(κ*t))≤η := by
      rcases hη with hη|hη
      · rw [hη,hT]; exact hanchor.1
      · rw [hη]; exact hηR
    let e : ProbabilityNode (sampleCorrelation η) ((d:ℝ)^(-(κ*w))) (n+1) := by
      simpa only [←hh,←hn] using C.sampleEndpoint η hηpos hηle
    have he := literalSample_cost_le_source (b:=κ*w) (by omega : 0<d) n m N nc Nc hradius hηle r e
    simpa only [cost_literalSample,hn,hN,hh,c] using he
  · exact hcap.trans (by nlinarith)

end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter Quadrature
open scoped Topology BigOperators Classical

lemma derivativeBudget_rate (m : ℕ) (a : ℝ) :
    LogPowerRate (fun d : ℕ => ∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/((d:ℝ)^(-a))|) (-a) := by
  apply ((LogPowerRate.inv_power a).const_mul (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j|)).congr
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  have hp : (0:ℝ)<d := by exact_mod_cast hd
  simp only [div_eq_mul_inv,abs_mul,abs_inv,abs_of_pos (Real.rpow_pos_of_pos hp (-a)),Finset.sum_mul]

theorem actualCoefficient_rate (n m nc : ℕ) {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    LogPowerRate (fun d : ℕ =>
      1+2*fixedCenteringBudget nc*((∑j,|terminalQuadratureWeight (sourceCorrelation a d) ((d:ℝ)^(-b)) n j|)*
        (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/((d:ℝ)^(-(4*a)))|)*
        (2*fixedProbabilityBudget n)+2)+4*fixedProbabilityBudget n+fixedHarmonicBudget n) (-(b+4*a)) := by
  obtain ⟨D,hD,hDu⟩ := exists_basisDerivative_budget (probabilityNodes (n+1))
  have he := sourceCorrelation_eventually ha
  have hm := sourceMesh_eventually ha hb
  have hq := terminalQuadratureWeight_rate n D (by linarith) hDu a b
    (he.mono (fun _ h => h.1)) (he.mono (fun _ h => h.2.1))
    (he.mono (fun _ h => h.2.2.le)) (hm.mono (fun _ h => h.1)) (hm.mono (fun _ h => h.2))
  have hs := derivativeBudget_rate m (4*a)
  have hr : LogPowerRate (fun d : ℕ =>
      (∑j,|terminalQuadratureWeight (sourceCorrelation a d) ((d:ℝ)^(-b)) n j|)*
        (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/((d:ℝ)^(-(4*a)))|)) (-(b+4*a)) := by
    simpa only [neg_add] using hq.mul hs
  have hc (c : ℝ) : LogPowerRate (fun _ : ℕ => c) (-(b+4*a)) :=
    (LogPowerRate.const c).mono (by linarith)
  exact (((hc 1).add ((hr.mul_const (2*fixedProbabilityBudget n)).add (hc 2) |>.const_mul
    (2*fixedCenteringBudget nc))).add (hc (4*fixedProbabilityBudget n))).add (hc (fixedHarmonicBudget n))
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter Quadrature MeanTree
open scoped Classical Topology

lemma source_angle_square {a : ℝ} (ha : 0<a) (m : ℕ) :
    ∀ᶠ d : ℕ in atTop,(((d:ℝ)^(-(4*a)))*(m:ℝ))^2≤(d:ℝ)^(-a) := by
  have he := (((LogPowerRate.power (4*a)).mul_const (m:ℝ)).pow 2).eventually_small
    (show a<(2:ℝ)*(4*a) by linarith)
  exact he.mono (fun d hd => (le_abs_self _).trans hd)

theorem exists_source_configuration {a b : ℝ} (ha : 0<a) (_ : 0<b)
    (n m N nc Nc : ℕ) : ∀ᶠ d : ℕ in atTop,∃C : CircuitParameters,
      C.n=n ∧ C.m=m ∧ C.N=N ∧ C.nc=nc ∧ C.Nc=Nc ∧
      C.T=sourceCorrelation a d ∧ C.h=(d:ℝ)^(-b) ∧ C.ψ=(d:ℝ)^(-(4*a)) ∧
      C.D=(d:ℝ)^a ∧ C.A=C.actualA ∧ C.Af=C.actualAf := by
  have ht := (sourceCorrelation_tendsto ha).eventually (lt_mem_nhds (by norm_num : (1/2:ℝ)<1))
  filter_upwards [sourceCorrelation_eventually ha,source_angle_square ha m,ht,eventually_ge_atTop (1:ℕ)] with d hd hangle hT hd1
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
  have hψ : 0<(d:ℝ)^(-(4*a)) := Real.rpow_pos_of_pos hd0 _
  have hroot : Real.sqrt (1-(sourceCorrelation a d)^2)=(d:ℝ)^(-a) := by
    rw [←hd.2.2,Real.sqrt_sq (Real.rpow_pos_of_pos hd0 (-a)).le]
  let C₀ : CircuitParameters := {
    n:=n, m:=m, N:=N, nc:=nc, Nc:=Nc,
    T:=sourceCorrelation a d, h:=(d:ℝ)^(-b), ψ:=(d:ℝ)^(-(4*a)),
    v:=(d:ℝ)^(-(4*a))*m, D:=(d:ℝ)^a, A:=1, Af:=1,
    T_lower:=hT.le, T_upper:=hd.2.1, h_pos:=Real.rpow_pos_of_pos hd0 _,
    v_nonneg:=by positivity,
    angle_bound:=by
      intro j
      have hj : 0≤angleNodes m j := by simp [angleNodes]
      have hjm : angleNodes m j ≤ (m : ℝ) := by
        dsimp [angleNodes]
        exact_mod_cast (Nat.le_of_lt_succ j.isLt)
      rw [abs_of_nonneg (mul_nonneg hψ.le hj)]
      exact mul_le_mul_of_nonneg_left hjm hψ.le,
    angle_small:=by rw [hroot]; exact hangle }
  let C := {C₀ with A:=C₀.actualA,Af:=C₀.actualAf}
  exact ⟨C,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem exists_subpower_routine_configuration {t κ : ℝ} (ht : 0<t) (hs : t≤1/44) (hκ : 0<κ)
    (N Nc : ℕ) (L : RoutineLabel) : ∃w : ℝ,0<w ∧ w<t ∧
      ∀n m nc,∀ᶠ d : ℕ in atTop,∃C : CircuitParameters,
        C.n=n ∧ C.m=m ∧ C.N=N ∧ C.nc=nc ∧ C.Nc=Nc ∧
        C.T=sourceCorrelation (κ*t) d ∧ C.h=(d:ℝ)^(-(κ*w)) ∧
        C.ψ=(d:ℝ)^(-(4*(κ*t))) ∧ C.D=(d:ℝ)^(κ*t) ∧ C.A=C.actualA ∧ C.Af=C.actualAf ∧
        ∀η₁ : ℝ,(d:ℝ)^(-(κ*t))≤η₁ → η₁≤1 →
        ∃B : ℕ,(B:ℝ)≤C.D ∧
          RoutineBudget B (Real.sqrt (1-C.T^2)/C.T) η₁ (constructRoutine d C ht hs L) := by
  obtain ⟨w,hw,hwt,hbudget⟩ := literal_recursive_budget_order ht hs hκ N Nc L
  refine ⟨w,hw,hwt,?_⟩
  intro n m nc
  filter_upwards [exists_source_configuration (mul_pos hκ ht) (mul_pos hκ hw) n m N nc Nc,
    hbudget n m nc] with d hC hB
  obtain ⟨C,hn,hm,hN,hnc,hNc,hT,hh,hψ,hD,hA,hAf⟩ := hC
  exact ⟨C,hn,hm,hN,hnc,hNc,hT,hh,hψ,hD,hA,hAf,hB C hn hm hN hnc hNc hT hh hD⟩
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter Quadrature
open scoped Classical Topology

structure SourceShape (κ t w : ℝ) (n N d : ℕ) (C : CircuitParameters) : Prop where
  n_eq : C.n=n
  m_eq : C.m=n
  N_eq : C.N=N
  nc_eq : C.nc=n
  Nc_eq : C.Nc=N
  T_eq : C.T=sourceCorrelation (κ*t) d
  h_eq : C.h=(d:ℝ)^(-(κ*w))
  ψ_eq : C.ψ=(d:ℝ)^(-(4*(κ*t)))
  D_eq : C.D=(d:ℝ)^(κ*t)
  A_eq : C.A=C.actualA
  Af_eq : C.Af=C.actualAf

def sourceA (κ t w : ℝ) (n d : ℕ) : ℝ :=
  1+2*fixedCenteringBudget n*((∑j,|terminalQuadratureWeight (sourceCorrelation (κ*t) d)
    ((d:ℝ)^(-(κ*w))) n j|)*(∑j : Fin (n+1),|derivativeWeight (angleNodes n) j/
      ((d:ℝ)^(-(4*(κ*t))))|)*(2*fixedProbabilityBudget n)+2)+
    4*fixedProbabilityBudget n+fixedHarmonicBudget n

def sourceAf (n : ℕ) : ℝ := 1+fixedCenteringBudget n+2*fixedProbabilityBudget n

lemma sourceAf_pos (n : ℕ) : 0<sourceAf n := by
  have hB := (fixedCenteringBudget_spec n).1
  have hP := (fixedProbabilityBudget_spec n).1
  unfold sourceAf
  positivity

lemma SourceShape.A {κ t w : ℝ} {n N d : ℕ} {C : CircuitParameters}
    (h : SourceShape κ t w n N d C) : C.A=sourceA κ t w n d := by
  rw [h.A_eq]
  unfold CircuitParameters.actualA CircuitParameters.quadratureBudget CircuitParameters.derivativeBudget
  rw [h.n_eq,h.m_eq,h.nc_eq,h.T_eq,h.h_eq,h.ψ_eq]
  rfl

lemma SourceShape.Af {κ t w : ℝ} {n N d : ℕ} {C : CircuitParameters}
    (h : SourceShape κ t w n N d C) : C.Af=sourceAf n := by
  rw [h.Af_eq,CircuitParameters.actualAf,h.nc_eq,h.n_eq]
  rfl

lemma SourceShape.depth {κ t w : ℝ} {n N d : ℕ} {C : CircuitParameters}
    (h : SourceShape κ t w n N d C) : C.depthBound=4*(N+1)^2 := by
  simp only [CircuitParameters.depthBound,h.N_eq]

lemma sourceA_rate {κ t w : ℝ} (hκ : 0<κ) (ht : 0<t) (hw : 0<w) (n : ℕ) :
    LogPowerRate (sourceA κ t w n) (-(κ*(w+4*t))) := by
  have h := actualCoefficient_rate n n n (mul_pos hκ ht) (mul_pos hκ hw)
  change LogPowerRate _ (-(κ*(w+4*t)))
  convert h using 1
  · rfl
  · ring

lemma exists_source_shape {κ t w : ℝ} (hκ : 0<κ) (ht : 0<t) (hw : 0<w) (n N : ℕ) :
    ∀ᶠ d : ℕ in atTop,∃C : CircuitParameters,SourceShape κ t w n N d C := by
  filter_upwards [exists_source_configuration (mul_pos hκ ht) (mul_pos hκ hw) n n N n N] with d hd
  obtain ⟨C,hn,hm,hN,hnc,hNc,hT,hh,hψ,hD,hA,hAf⟩ := hd
  exact ⟨C,hn,hm,hN,hnc,hNc,hT,hh,hψ,hD,hA,hAf⟩
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter
open scoped Classical Topology

def meanFinalSize (κ t : ℝ) (n : ℕ) (q : ℕ → ℝ) (d : ℕ) : ℝ :=
  (1+4*sourceAf n)*(d:ℝ)^(-(κ*t))*q d

def sampleFinalSize (n : ℕ) (q : ℕ → ℝ) (d : ℕ) : ℝ := (1+4*sourceAf n)*q d

def internalSize (κ t w : ℝ) (n : ℕ) (q : ℕ → ℝ) (d : ℕ) : ℝ :=
  q d*(1+16*(d:ℝ)^(κ*t)*sourceA κ t w n d/((d:ℝ)^(-(κ*t))))

def anchorSize (κ t : ℝ) (q : ℕ → ℝ) (d : ℕ) : ℝ := q d/((d:ℝ)^(-(κ*t)))

lemma meanFinalSize_rate {κ t b : ℝ} (n : ℕ) {q : ℕ → ℝ}
    (hq : LogPowerRate q (κ*b)) : LogPowerRate (meanFinalSize κ t n q) (κ*(b+t)) := by
  have h := ((LogPowerRate.power (κ*t)).const_mul (1+4*sourceAf n)).mul hq
  convert h using 1
  · rfl
  · ring

lemma sampleFinalSize_rate {κ b : ℝ} (n : ℕ) {q : ℕ → ℝ}
    (hq : LogPowerRate q (κ*b)) : LogPowerRate (sampleFinalSize n q) (κ*b) :=
  hq.const_mul _

lemma internalSize_rate {κ t w b : ℝ} (hκ : 0<κ) (ht : 0<t) (hw : 0<w) (hwt : w<t)
    (n : ℕ) {q : ℕ → ℝ} (hq : LogPowerRate q (κ*b)) :
    LogPowerRate (internalSize κ t w n q) (κ*(b-10*t)) := by
  have hD := LogPowerRate.power (-(κ*t))
  have hA := sourceA_rate hκ ht hw n
  have hR := LogPowerRate.inv_power (κ*t)
  have he := (((hD.const_mul 16).mul hA).mul hR)
  have he' : LogPowerRate (fun d => 16*(d:ℝ)^(κ*t)*sourceA κ t w n d/((d:ℝ)^(-(κ*t))))
      (-(κ*(w+6*t))) := by
    convert he using 1
    · funext d; simp only [neg_neg,div_eq_mul_inv]
    · ring
  have hc := (LogPowerRate.const 1).mono (show -(κ*(w+6*t))≤0 by nlinarith)
  have hi := hq.mul (hc.add he')
  have him := hi.mono (show κ*(b-10*t)≤κ*b+ -(κ*(w+6*t)) by nlinarith)
  exact him

lemma anchorSize_rate {κ t b : ℝ} (hκ : 0≤κ) (ht : 0≤t)
    {q : ℕ → ℝ} (hq : LogPowerRate q (κ*b)) :
    LogPowerRate (anchorSize κ t q) (κ*(b-10*t)) := by
  have h := hq.mul (LogPowerRate.inv_power (κ*t))
  have hm := h.mono (show κ*(b-10*t)≤κ*b+ -(κ*t) by nlinarith)
  change LogPowerRate (fun d => q d/((d:ℝ)^(-(κ*t)))) _
  simpa only [div_eq_mul_inv] using hm

lemma small_coefficient_rate {κ t w b : ℝ} (hκ : 0<κ) (ht : 0<t) (hw : 0<w)
    (hwt : w<t) (hts : t<1/100) (hb : 1/2≤b) (n : ℕ)
    {q : ℕ → ℝ} (hq : LogPowerRate q (κ*b)) :
    LogPowerRate (fun d => sourceA κ t w n d*q d) (κ/3) := by
  exact ((sourceA_rate hκ ht hw n).mul hq).mono (by nlinarith)

lemma parent_intrinsic_rate {κ b p : ℝ} (hκ : 0≤κ) (hb : 1/2≤b)
    {q e : ℕ → ℝ} (hq : LogPowerRate q (κ*b)) (he : LogPowerRate e (κ*(p-1/4))) :
    LogPowerRate (fun d => q d*e d) (κ*p) :=
  (hq.mul he).mono (by nlinarith)

lemma meanError_rate {κ J b p : ℝ} (hκ : 0≤κ) (hb : 1/2≤b) (hp : p≤J)
    (Af H Kf : ℝ) {q es ei ef : ℕ → ℝ} (hq : LogPowerRate q (κ*b))
    (hes : LogPowerRate es (κ*(p-1/4))) (hei : LogPowerRate ei (κ*(p-1/4)))
    (hef : LogPowerRate ef (κ*p)) :
    LogPowerRate (fun d => 2*Af*Kf*H*q d*es d+
      10*(20+16*circuitGrowthConstant^2)*(2*(1+2*H)*(Af*Kf*q d*ei d+ef d))+
      2*(d:ℝ)^(-(κ*J))) (κ*p) := by
  have he := (parent_intrinsic_rate hκ hb hq hei).const_mul (Af*Kf)
  have hc := (he.add hef).const_mul (2*(1+2*H)) |>.const_mul (10*(20+16*circuitGrowthConstant^2))
  have ha := (parent_intrinsic_rate hκ hb hq hes).const_mul (2*Af*Kf*H)
  have hn := ((LogPowerRate.power (κ*J)).mono (show κ*p≤κ*J by nlinarith)).const_mul 2
  apply ((ha.add hc).add hn).congr
  filter_upwards [] with d
  ring

lemma sampleError_rate {κ J b p : ℝ} (hκ : 0≤κ) (hb : 1/2≤b) (hp : p≤J)
    (Af H Kf : ℝ) {q ei ef : ℕ → ℝ} (hq : LogPowerRate q (κ*b))
    (hei : LogPowerRate ei (κ*(p-1/4))) (hef : LogPowerRate ef (κ*p)) :
    LogPowerRate (fun d => 20*(2*(1+2*H)*(Af*Kf*q d*ei d+ef d))+
      2*(d:ℝ)^(-(κ*J))) (κ*p) := by
  have he := (parent_intrinsic_rate hκ hb hq hei).const_mul (Af*Kf)
  have hc := (he.add hef).const_mul (2*(1+2*H)) |>.const_mul 20
  have hn := ((LogPowerRate.power (κ*J)).mono (show κ*p≤κ*J by nlinarith)).const_mul 2
  apply (hc.add hn).congr
  filter_upwards [] with d
  ring
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open scoped Classical

def RoutineLabel.Admissible (t K : ℝ) (L : RoutineLabel) : Prop :=
  0≤L.p ∧ L.p≤K ∧ 1/2+40*t*L.p≤L.b

lemma RoutineLabel.Admissible.b_lower {t K : ℝ} {L : RoutineLabel}
    (h : L.Admissible t K) (ht : 0≤t) : 1/2≤L.b := by
  have he : 0≤40*t*L.p := by positivity [h.1]
  linarith [h.2.2]

lemma RoutineLabel.Admissible.child {t K : ℝ} {P C : RoutineLabel}
    (h : P.Admissible t K) (ht : 0≤t) (hnt : ¬P.terminal)
    (hc : RoutineStep t P C) : C.Admissible t K := by
  have hb := h.b_lower ht
  have hp : P.b<P.p := lt_of_not_ge hnt
  cases hc with
  | meanFinal b p =>
    rcases h with ⟨hp0,hpK,hbp⟩
    dsimp only [RoutineLabel.Admissible] at *
    exact ⟨hp0,hpK,by linarith⟩
  | sampleFinal b p => exact h
  | internal k k' b p =>
    rcases h with ⟨hp0,hpK,hbp⟩
    dsimp only [RoutineLabel.Admissible] at *
    exact ⟨by linarith,by linarith,by nlinarith⟩

lemma RoutineLabel.Admissible.rank_bound {t K : ℝ} {L : RoutineLabel}
    (h : L.Admissible t K) (ht : 0<t) : L.rank t≤2*⌈K/t⌉₊+1 := by
  have hb := h.b_lower ht.le
  have hn : ⌈(L.p-L.b)/t⌉₊≤⌈K/t⌉₊ := Nat.ceil_mono
    (div_le_div_of_nonneg_right (by linarith [h.2.1]) ht.le)
  unfold RoutineLabel.rank
  cases L.kind <;> dsimp only <;> omega

lemma topLabel_admissible {t K : ℝ} (hK : 0≤K) (ht : 0≤t)
    (hsmall : 40*(K+2)*t<1/4) : (⟨.sample,1,K⟩:RoutineLabel).Admissible t K := by
  refine ⟨hK,le_rfl,?_⟩
  dsimp
  nlinarith
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter Quadrature MeanTree
open scoped Classical Topology

theorem exists_uniform_routine_mesh {κ t K : ℝ} (hκ : 0<κ) (ht : 0<t) (hts : t≤1/44)
    (N : ℕ) : ∃w : ℝ,0<w ∧ w<t ∧ ∀n : ℕ,
      ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,SourceShape κ t w n N d C →
      ∃B : ℕ,(B:ℝ)≤C.D ∧
      ∀L : RoutineLabel,L.Admissible t K → ∀η₁ : ℝ,(d:ℝ)^(-(κ*t))≤η₁ → η₁≤1 →
      RoutineBudget B (Real.sqrt (1-C.T^2)/C.T) η₁ (constructRoutine d C ht hts L) := by
  let rank := 2*⌈K/t⌉₊+1
  obtain ⟨w,hw,hwt,hcost⟩ := exists_cost_mesh_exponent ht hκ N N rank
  refine ⟨w,hw,hwt,?_⟩
  intro n
  filter_upwards [hcost n n n,source_anchor_radius (mul_pos hκ ht),eventually_ge_atTop (1:ℕ)] with d hd hanchor hd1
  intro C hC
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd1
  have hdge : (1:ℝ)≤d := by exact_mod_cast hd1
  have hDpos : 0<C.D := by rw [hC.D_eq]; exact Real.rpow_pos_of_pos hd0 _
  have hDone : 1≤C.D := by rw [hC.D_eq]; exact Real.one_le_rpow hdge (mul_pos hκ ht).le
  let c := sourceOccurrenceBudget (κ*t) (κ*w) n n N n N d
  let B := 2*(40*c+40)^rank
  have hcap : (B:ℝ)≤C.D := by simpa only [B,c,hC.D_eq] using hd
  refine ⟨B,hcap,?_⟩
  intro L hL η₁ hηR hη1
  have hmono : 2*(40*c+40)^L.rank t≤B := by
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_right (by omega : 1≤40*c+40) (hL.rank_bound ht)
  apply RoutineBudget.mono (hBC:=hmono)
  apply constructRoutine_budget C ht hts c η₁ hDpos
  · intro r σ
    unfold CircuitParameters.meanTree
    rw [cost_literalMean]
    simp only [hC.n_eq,hC.m_eq,hC.N_eq,hC.nc_eq,hC.Nc_eq,hC.T_eq,hC.h_eq]
    unfold c sourceOccurrenceBudget
    omega
  · intro r η hη hηpos hηle
    unfold CircuitParameters.sampleTree
    have hradius : (d:ℝ)^(-(κ*t))≤η := by
      rcases hη with hη|hη
      · rw [hη,hC.T_eq]; exact hanchor.1
      · rw [hη]; exact hηR
    let e : ProbabilityNode (sampleCorrelation η) ((d:ℝ)^(-(κ*w))) (n+1) := by
      simpa only [←hC.h_eq,←hC.n_eq] using C.sampleEndpoint η hηpos hηle
    have he := literalSample_cost_le_source (b:=κ*w) (by omega : 0<d) n n N n N hradius hηle r e
    simpa only [cost_literalSample,hC.n_eq,hC.N_eq,hC.h_eq,c] using he
  · have hmreal : ((2*(40*c+40)^L.rank t:ℕ):ℝ)≤B := by exact_mod_cast hmono
    have hreal : ((2*(40*c+40)^L.rank t:ℕ):ℝ)≤C.D := hmreal.trans hcap
    exact hreal.trans (by nlinarith)
end LogConcaveSampling.OracleCompiler

end

end

end OAI
