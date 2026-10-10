import OAI.Combinatorics.ContingencyTables.Machines.ScalarScheduleProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedCountingSchedule

namespace OAI

/-! # Fixed arithmetic circuits for the phase scalar controls -/

namespace ContingencyTables.CountingPhaseScalarProgram
open ScalarScheduleProgram
open MatchingFPRAS.TreeTyped

/-- Field order: label count, cutoff, phase count, restart time,
observation count, return cap, capacity-bit allowance. -/
def p : Expr := .input 0
def w : Expr := .input 1
def h : Expr := .input 2
def tau : Expr := .input 3
def observations : Expr := .input 4
def returns : Expr := .input 5
def capacityBits : Expr := .input 6

def observable : Expr := 10*p^4*(9*(p*(1+8*p*w^4))+2*(8+32*p*w^6))
def observationNumerator : Expr := 1024*(h+1)*(32000*p^8*observable)
def restartTime : Expr := 4*observable*(h+p+capacityBits+5)
def returnCap : Expr := 65536*(h+1)^2*(tau+1)*(p^2+1)
def precisionBase : Expr := 1024*(h+1)*(8*(observations+1)+8*h*tau*(returns+1))+1
def initialPrecision : Expr := 2048*(h+1)

lemma observable_value (P W H T N R L : ℕ) :
    observable.eval [P,W,H,T,N,R,L]=CountingPhaseSchedule.observable P W := by
  simp [observable,p,w,Expr.eval,CountingPhaseSchedule.observable]

lemma observationNumerator_value (P W H T N R L : ℕ) :
    observationNumerator.eval [P,W,H,T,N,R,L]=
      1024*(H+1)*CountingPhaseSchedule.observationCoefficient P W := by
  simp [observationNumerator,observable,p,w,h,Expr.eval,
    CountingPhaseSchedule.observationCoefficient,CountingPhaseSchedule.observable]

lemma returnCap_value (P W H T N R L : ℕ) :
    returnCap.eval [P,W,H,T,N,R,L]=CountingPhaseSchedule.returnCap P H T := by
  simp [returnCap,p,h,tau,Expr.eval,CountingPhaseSchedule.returnCap]

lemma precisionBase_value (P W H T N R L : ℕ) :
    precisionBase.eval [P,W,H,T,N,R,L]=
      1024*(H+1)*CountingPhaseSchedule.noiseCoefficient H T N R+1 := by
  simp [precisionBase,h,tau,observations,returns,Expr.eval,CountingPhaseSchedule.noiseCoefficient]

lemma initialPrecision_value (P W H T N R L : ℕ) :
    initialPrecision.eval [P,W,H,T,N,R,L]=CountingPhaseSchedule.initialPrecision H := by
  simp [initialPrecision,h,Expr.eval,CountingPhaseSchedule.initialPrecision]

lemma restartTime_instance {I J : Type} [Fintype I] [Fintype J]
    (A : CompanionFactorialApplication.Instance I J) (H L T N R : ℕ) :
    restartTime.eval [Fintype.card (CompanionFactorialApplication.Labels A),A.W,H,T,N,R,L]=
      CompanionTargetMixing.restartTime A H L := by
  simp [restartTime,observable,p,w,h,capacityBits,Expr.eval,
    CompanionTargetMixing.restartTime,CompanionTrace.time,CompanionTrace.integerConstant]
  ring

/-- Every circuit above has a fixed polynomial binary-time implementation. -/
lemma polynomial (e : Expr) : PolynomialTime e.realizer := e.polynomial

end ContingencyTables.CountingPhaseScalarProgram

end OAI
