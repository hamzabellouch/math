import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SharpWindowIocAdd
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CellSumFull

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryLocalAdditive
open OrdinaryCorrelations OrdinarySharpWindow Finset MeasureTheory OrdinaryDiscreteWindows
lemma dyadic_l1_le_discrete {a : ℕ→ℂ} (ha : OneBounded a) (X D : ℕ) :
    (∫x:ℝ,‖sharpWindow (Ioc X (2*X)) a (fun n=>(n:ℝ)) (D:ℝ) x‖) ≤
      (∑y∈range X,‖∑k∈range D,a (y+1+k)‖)+
      (∑y∈range (2*X),‖∑k∈range D,a (y+1+k)‖)+4*(D:ℝ)^2 := by
  have hh := sharpWindow_Ioc_l1 a (fun n=>(n:ℝ)) (D:ℝ) (X:=0) (A:=X) (B:=2*X) (by omega) (by omega)
  have h1 := prefix_l1_le_short_norm ha X D
  have h2 := prefix_l1_le_short_norm ha (2*X) D
  linarith only [hh,h1,h2]
end OrdinaryLocalAdditive

end

end OAI
