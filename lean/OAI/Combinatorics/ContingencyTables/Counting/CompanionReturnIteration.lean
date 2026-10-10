import OAI.Combinatorics.ContingencyTables.Counting.CompanionWarmReturn
import OAI.Combinatorics.ContingencyTables.Counting.CompanionTargetMixing
import OAI.Combinatorics.ContingencyTables.Transport.WarmKernelIteration

namespace OAI

/-! # Repeated bounded returns to the literal companion law

Only the exact reference trajectory is required to remain warm. The
actual finite-word return kernel can accumulate its error without any
additional warmness hypothesis on its output.
-/

namespace ContingencyTables.CompanionReturnIteration

open CommonBasesFPRAS RealKernelApproximation CompanionFactorialApplication
open CompanionBooleanPhase CompanionOracleDensity CompanionRationalUpdates
open CompanionWarmReturn CompanionTargetTrace CompanionTargetMixing
open CompanionAnnealing CompanionWarmStart TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

theorem reference_mixing_distance (A : Instance I J) (H L j : ℕ) (hj : j≤H)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1))≤(2:ℝ)^L)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A j) (fun p q => (w p q:ℝ)))
    (nu : PlainIndex (pairs : List (Pair A)) → ℝ) (hnu : ∀ S,0≤nu S)
    (hmass : ∑ S,nu S=1) (t : ℕ) :
    distance (((CompanionTargetTrace.actualTrace A j hp w hw).kernel.power t).push nu)
      (fun S => law A j S.val.val)≤
        (Real.exp (-(t:ℝ)/(2*ObservableBounds.observableConstant
          (Fintype.card (Labels A)) ((A.W:ℝ)^2)))/CompanionTrace.minimumMass A H L)/2 := by
  let D := CompanionTargetTrace.actualTrace A j hp w hw
  have hmix (x y : PlainIndex (pairs : List (Pair A))) :
      |(D.kernel.power t).P x y/D.π y-1|≤
        Real.exp (-(t:ℝ)/(2*ObservableBounds.observableConstant
          (Fintype.card (Labels A)) ((A.W:ℝ)^2)))/CompanionTrace.minimumMass A H L := by
    rw [actualTrace_pi]
    exact target_point_mixing A H L j hj hbox hp w hw hgood t x y
  have hm := WarmKernelIteration.mixing_distance D nu hnu hmass t _ hmix
  have hpi : D.π=(fun S => law A j S.val.val) := by
    funext S
    exact actualTrace_pi A j hp w hw S
  rw [hpi] at hm
  exact hm

theorem repeated_return_distance (A : Instance I J) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A j) (fun p q => (w p q:ℝ)))
    (hn : 0<n) (nu : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hnu : ∀ S,0≤nu S) (hmass : ∑ S,nu S≤1) (U : ℝ) (hU : 0≤U)
    (hwarm : ∀ S,nu S≤U*law A j S.val.val) (t : ℕ) :
    distance (((returnKernel A C K j k n hK hW xi v w).power t).push nu)
      (((CompanionTargetTrace.actualTrace A j hp w hw).kernel.power t).push nu)≤
        (t:ℝ)*((5*(Fintype.card (Labels A):ℝ)^2*U)/(n:ℝ)+
          ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)) := by
  have hwar : ∀ S,nu S≤U*(CompanionTargetTrace.actualTrace A j hp w hw).π S := by
    intro S
    rw [actualTrace_pi]
    exact hwarm S
  have hstep (rho : PlainIndex (pairs : List (Pair A)) → ℝ)
      (hrho : ∀ S,0≤rho S) (hrmass : ∑ S,rho S≤1)
      (hrwarm : ∀ S,rho S≤U*(CompanionTargetTrace.actualTrace A j hp w hw).π S) :=
    warm_return_distance A C hC K j k n hK hW hB hj xi hx0 hx1 hPL hCheeger
      v hp w hw hgood hn rho hrho hrmass U hU
      (fun S => by simpa only [actualTrace_pi] using hrwarm S)
  exact WarmKernelIteration.power_distance
    (CompanionTargetTrace.actualTrace A j hp w hw)
    (returnKernel A C K j k n hK hW xi v w) nu hnu hmass U _ hwar hstep t

/-- The terminal law after repeated actual Boolean returns. The first
term is the accumulated implementation error; the second is mixing of
the exact literal trace. -/
theorem repeated_return_stationary (A : Instance I J) (C : ℕ) (hC : 0<C)
    (K H L j k n : ℕ) (hK : 1≤K) (hW : 100*A.d*K≤A.W)
    (hB : (K:ℝ)=binWidth A C) (hj : j≤rationalHeight A C) (hjH : j≤H)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1))≤(2:ℝ)^L)
    (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A j) (fun p q => (w p q:ℝ)))
    (hn : 0<n) (nu : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hnu : ∀ S,0≤nu S) (hmass : ∑ S,nu S=1) (U : ℝ) (hU : 0≤U)
    (hwarm : ∀ S,nu S≤U*law A j S.val.val) (t : ℕ) :
    distance (((returnKernel A C K j k n hK hW xi v w).power t).push nu)
      (fun S => law A j S.val.val)≤
        (t:ℝ)*((5*(Fintype.card (Labels A):ℝ)^2*U)/(n:ℝ)+
          ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2))+
        (Real.exp (-(t:ℝ)/(2*ObservableBounds.observableConstant
          (Fintype.card (Labels A)) ((A.W:ℝ)^2)))/CompanionTrace.minimumMass A H L)/2 := by
  have hr := repeated_return_distance A C hC K j k n hK hW hB hj xi hx0 hx1
    hPL hCheeger v hp w hw hgood hn nu hnu hmass.le U hU hwarm t
  have hm := reference_mixing_distance A H L j hjH hbox hp w hw hgood nu hnu hmass t
  have ht := distance_triangle
    (((returnKernel A C K j k n hK hW xi v w).power t).push nu)
    (((CompanionTargetTrace.actualTrace A j hp w hw).kernel.power t).push nu)
    (fun S => law A j S.val.val)
  exact ht.trans (_root_.add_le_add hr hm)

end
end ContingencyTables.CompanionReturnIteration

end OAI
