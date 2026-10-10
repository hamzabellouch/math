import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.RoutineKind
import OAI.Probability.LogConcave.Numerics.CompileDeclaredRootShift
import OAI.Probability.LogConcave.OraclePrograms.TerminalMeanProgram
import OAI.Probability.LogConcave.Sampling.SampleCorrelation

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree Quadrature
open scoped Classical

structure CircuitParameters where
  n : ℕ
  m : ℕ
  N : ℕ
  nc : ℕ
  Nc : ℕ
  T : ℝ
  h : ℝ
  ψ : ℝ
  v : ℝ
  D : ℝ
  A : ℝ
  Af : ℝ
  T_lower : 1/2≤T
  T_upper : T<1
  h_pos : 0<h
  v_nonneg : 0≤v
  angle_bound : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v
  angle_small : v^2≤Real.sqrt (1-T^2)

namespace CircuitParameters
variable (C : CircuitParameters) {d : ℕ}

def meanEndpoint : ProbabilityNode C.T C.h (C.n+1) :=
  probabilityEndpoint (by linarith [C.T_lower]) C.T_upper C.h_pos (C.n+1)

def meanTree (r σ : ℝ) : MeanTree (MeanInput d) d :=
  literalMean r C.T C.h C.ψ σ C.n C.m C.N C.nc C.Nc C.meanEndpoint

def meanDrift (r σ : ℝ) (hr : 0<r) : DriftData (C.meanTree (d:=d) r σ) :=
  (literalMean_drift hr C.T_lower C.T_upper C.h_pos C.v_nonneg C.angle_small C.angle_bound C.meanEndpoint).choose

lemma meanDrift_spec (r σ : ℝ) (hr : 0<r) :
    DriftValid (meanInputMove r C.T) (C.meanTree (d:=d) r σ) (C.meanDrift r σ hr) ∧
      (C.meanDrift (d:=d) r σ hr).root _=0 ∧ DriftBound 3 _ (C.meanDrift (d:=d) r σ hr) :=
  (literalMean_drift hr C.T_lower C.T_upper C.h_pos C.v_nonneg C.angle_small C.angle_bound C.meanEndpoint).choose_spec

def sampleEndpoint (η : ℝ) (hη : 0<η) (hη1 : η≤1) :
    ProbabilityNode (sampleCorrelation η) C.h (C.n+1) :=
  probabilityEndpoint (by linarith [(sampleCorrelation_properties hη hη1).1])
    (sampleCorrelation_properties hη hη1).2.1 C.h_pos (C.n+1)

def sampleTree (r η : ℝ) (hη : 0<η) (hη1 : η≤1) : MeanTree (SampleInput d) d :=
  literalSample r (sampleCorrelation η) C.h (C.n+1) C.N (C.sampleEndpoint η hη hη1)

def sampleDrift (r η : ℝ) (hr : 0<r) (hη : 0<η) (hη1 : η≤1) :
    DriftData (C.sampleTree (d:=d) r η hη hη1) :=
  (literalSample_drift hr (Nat.succ_pos C.n)
    (by linarith [(sampleCorrelation_properties hη hη1).1])
    (sampleCorrelation_properties hη hη1).2.1 C.h_pos (C.sampleEndpoint η hη hη1)).choose

def meanCenterBudget (r σ : ℝ) : ℝ := C.A*(r/σ+r^2)
def sampleCenterBudget (r : ℝ) : ℝ := C.A*r^2
def sampleFinalBudget (r : ℝ) : ℝ := C.Af*r

def meanFrom (Mf Mi : ℝ → ℝ → SeedProgram d) (S : ℝ → ℝ → ReservedProgram d)
    (r σ : ℝ) : SeedProgram d :=
  if hr : 0<r then
    let E := C.meanTree r σ
    let p := C.meanDrift r σ hr
    let noise := Real.sqrt 3*σ/2
    let B := compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi E noise
    let v := compileDeclaredRootShift C.D (C.meanCenterBudget r σ) C.Af Mf Mi E noise p
    let R := Real.sqrt (1-C.T^2)
    let anchor := S r (R/C.T)
    meanParent anchor.full B (anchor.extraShift (-2*R/C.T)) v C.T
  else terminalMeanProgram d r σ

def sampleFrom (Mf Mi : ℝ → ℝ → SeedProgram d) (r η : ℝ) : ReservedProgram d :=
  if hv : 0<r ∧ 0<η ∧ η≤1 then
    let E := C.sampleTree r η hv.2.1 hv.2.2
    let p := C.sampleDrift r η hv.1 hv.2.1 hv.2.2
    let noise := η/Real.sqrt 2
    let B := compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi E noise
    let v := compileDeclaredRootShift C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi E noise p
    sampleParent B v (sampleCorrelation η) η
  else terminalReservedProgram d r η
end CircuitParameters

def RoutineValue (d : ℕ) : RoutineKind → Type
  | .mean => ℝ → ℝ → SeedProgram d
  | .sample => ℝ → ℝ → ReservedProgram d

def constructRoutine (d : ℕ) (C : CircuitParameters) {t : ℝ} (ht : 0<t) (hs : t≤1/44)
    (L : RoutineLabel) : RoutineValue d L.kind :=
  if _ : L.terminal then
    match L.kind with
    | .mean => terminalMeanProgram d
    | .sample => terminalReservedProgram d
  else
    match hk : L.kind with
    | .mean => C.meanFrom
        (constructRoutine d C ht hs ⟨.mean,L.b+t,L.p⟩)
        (constructRoutine d C ht hs ⟨.mean,L.b-10*t,L.p-1/4⟩)
        (constructRoutine d C ht hs ⟨.sample,L.b-10*t,L.p-1/4⟩)
    | .sample => C.sampleFrom
        (constructRoutine d C ht hs ⟨.mean,L.b,L.p⟩)
        (constructRoutine d C ht hs ⟨.mean,L.b-10*t,L.p-1/4⟩)
termination_by L.rank t
decreasing_by
  all_goals apply RoutineStep.rank_lt ht hs (by assumption)
  · simpa only [←hk] using (RoutineStep.meanFinal (t:=t) L.b L.p)
  · simpa only [←hk] using (RoutineStep.internal (t:=t) RoutineKind.mean RoutineKind.mean L.b L.p)
  · simpa only [←hk] using (RoutineStep.internal (t:=t) RoutineKind.mean RoutineKind.sample L.b L.p)
  · simpa only [←hk] using (RoutineStep.sampleFinal (t:=t) L.b L.p)
  · simpa only [←hk] using (RoutineStep.internal (t:=t) RoutineKind.sample RoutineKind.mean L.b L.p)
end LogConcaveSampling.OracleCompiler

end

end

end OAI
