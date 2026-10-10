import OAI.Combinatorics.ContingencyTables.Rooted.RootedReturnIteration
import OAI.Combinatorics.ContingencyTables.Counting.CompanionReturnWords
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordDependent
import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanWalk

namespace OAI

/-! # A fixed Boolean word for selected-root repeated capped returns

The restart routine iterates the actual defaulted return experiment.
Every iteration receives a disjoint block, and an optional initial
finite-word draw receives its own disjoint block as well.
-/

namespace ContingencyTables.RootedReturnWords

open CommonBasesFPRAS ResidualMixture FirstSuccess FairBits RealKernelApproximation
open CompanionFactorialApplication RootedBooleanPhase CompanionOracleDensity
open CompanionBooleanPhase (stepBits)
open CompanionReturnWords (returnBits)
open RootedCappedReturn RootedWarmReturn RootedReturnIteration
open CompanionRationalUpdates RootedAnnealing TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

private theorem walkLaw_cast_power {X : Type*} [Fintype X] [DecidableEq X]
    (Q : X → RationalLaw X) (x : X) (n : ℕ) (y : X) :
    ((walkLaw Q x n).mass y:ℝ)=((rationalKernel Q).power n).P x y := by
  induction n generalizing y with
  | zero =>
    simp only [walkLaw,pointLaw,FiniteKernel.power,FiniteKernel.identity]
    by_cases h : x=y
    · subst y; simp
    · simp [h,Ne.symm h]
  | succ n ih =>
    change ((∑ z,(walkLaw Q x n).mass z*(Q z).mass y:ℚ):ℝ)=_
    simp only [Rat.cast_sum,Rat.cast_mul,ih,
      FiniteKernel.power,FiniteKernel.comp,rationalKernel]

variable {I J : Type} [Fintype I] [Fintype J]

def booleanReturns (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n t : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A)))
    (bits : Fin (returnBits A C K j k n t xi) → Bool) :
    PlainIndex (pairs : List (Pair A)) :=
  wordWalk (returnWordDefault A R C K j k n hK hW xi v w) S t
    (gridWordEquiv t ((n+1)*stepBits A C K j k xi) bits)

def booleanReturnsLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n t : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A))) :
    RationalLaw (PlainIndex (pairs : List (Pair A))) :=
  mapLaw (uniformLaw (α := Fin (returnBits A C K j k n t xi) → Bool))
    (booleanReturns A R C K j k n t hK hW xi v w S)

theorem booleanReturnsLaw_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n t : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A))) :
    booleanReturnsLaw A R C K j k n t hK hW xi v w S=
      walkLaw (returnLaw A R C K j k n hK hW xi v w) S t := by
  let step := returnWordDefault A R C K j k n hK hW xi v w
  change mapLaw (uniformLaw (α := Fin (t*((n+1)*stepBits A C K j k xi)) → Bool))
    (fun bits => wordWalk step S t
      (gridWordEquiv t ((n+1)*stepBits A C K j k xi) bits))=_
  have he := map_equiv (gridWordEquiv t ((n+1)*stepBits A C K j k xi))
    (uniformLaw (α := Fin (t*((n+1)*stepBits A C K j k xi)) → Bool))
    (wordWalk step S t)
  rw [uniform_equiv] at he
  exact he.symm.trans (wordWalkLaw_eq step S t)

theorem booleanReturnsLaw_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n t : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S T : PlainIndex (pairs : List (Pair A))) :
    ((booleanReturnsLaw A R C K j k n t hK hW xi v w S).mass T:ℝ)=
      ((returnKernel A R C K j k n hK hW xi v w).power t).P S T := by
  rw [booleanReturnsLaw_eq]
  exact walkLaw_cast_power (returnLaw A R C K j k n hK hW xi v w) S t T

def initializedReturns (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n t r : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (initial : (Fin r → Bool) → PlainIndex (pairs : List (Pair A)))
    (bits : Fin (r+returnBits A C K j k n t xi) → Bool) :
    PlainIndex (pairs : List (Pair A)) :=
  let b := splitWordEquiv r (returnBits A C K j k n t xi) bits
  booleanReturns A R C K j k n t hK hW xi v w (initial b.1) b.2

def initializedReturnsLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n t r : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (initial : (Fin r → Bool) → PlainIndex (pairs : List (Pair A))) :
    RationalLaw (PlainIndex (pairs : List (Pair A))) :=
  mapLaw (uniformLaw (α := Fin (r+returnBits A C K j k n t xi) → Bool))
    (initializedReturns A R C K j k n t r hK hW xi v w initial)

theorem initializedReturnsLaw_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n t r : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (initial : (Fin r → Bool) → PlainIndex (pairs : List (Pair A))) :
    initializedReturnsLaw A R C K j k n t r hK hW xi v w initial=
      bindLaw (mapLaw (uniformLaw (α := Fin r → Bool)) initial)
        (booleanReturnsLaw A R C K j k n t hK hW xi v w) := by
  unfold initializedReturnsLaw initializedReturns
  dsimp only
  have he := map_equiv (splitWordEquiv r (returnBits A C K j k n t xi))
    (uniformLaw (α := Fin (r+returnBits A C K j k n t xi) → Bool))
    (fun b => booleanReturns A R C K j k n t hK hW xi v w (initial b.1) b.2)
  rw [uniform_equiv,←uniform_product] at he
  exact he.symm.trans (mapLaw_product_finish _ _ initial
    (booleanReturns A R C K j k n t hK hW xi v w))

theorem initializedReturnsLaw_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n t r : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (initial : (Fin r → Bool) → PlainIndex (pairs : List (Pair A)))
    (T : PlainIndex (pairs : List (Pair A))) :
    ((initializedReturnsLaw A R C K j k n t r hK hW xi v w initial).mass T:ℝ)=
      ((returnKernel A R C K j k n hK hW xi v w).power t).push
        (fun S => ((mapLaw (uniformLaw (α := Fin r → Bool)) initial).mass S:ℝ)) T := by
  rw [initializedReturnsLaw_eq]
  simp only [bindLaw,Rat.cast_sum,Rat.cast_mul,booleanReturnsLaw_cast,FiniteKernel.push]

/-- The initial word need only be close in total variation to a warm
reference law. No pointwise warmness of the actual initial word law is
assumed. -/
theorem initializedReturns_distance (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C)
    (K H L j k n t r : ℕ) (hK : 1≤K) (hW : 100*A.d*K≤A.W)
    (hB : (K:ℝ)=binWidth A C) (hj : j≤rationalHeight A C) (hjH : j≤H)
    (hbox : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1))≤(2:ℝ)^L)
    (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (hn : 0<n) (nu : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hnu : ∀ S,0≤nu S) (hmass : ∑ S,nu S=1) (U : ℝ) (hU : 0≤U)
    (hwarm : ∀ S,nu S≤U*RootedWarmStart.law A R j S.val.val)
    (initial : (Fin r → Bool) → PlainIndex (pairs : List (Pair A))) :
    distance
      (fun T => ((initializedReturnsLaw A R C K j k n t r hK hW xi v w initial).mass T:ℝ))
      (fun S => RootedWarmStart.law A R j S.val.val)≤
        distance (fun S => ((mapLaw (uniformLaw (α := Fin r → Bool)) initial).mass S:ℝ)) nu+
        ((t:ℝ)*((5*(Fintype.card (Labels A):ℝ)^2*U)/(n:ℝ)+
          ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2))+
        (Real.exp (-(t:ℝ)/(2*ObservableBounds.observableConstant
          (Fintype.card (Labels A)) ((A.W:ℝ)^2)))/CompanionTrace.minimumMass A H L)/2) := by
  let p : PlainIndex (pairs : List (Pair A)) → ℝ := fun S =>
    ((mapLaw (uniformLaw (α := Fin r → Bool)) initial).mass S:ℝ)
  let Q := (returnKernel A R C K j k n hK hW xi v w).power t
  have he :
      (fun T => ((initializedReturnsLaw A R C K j k n t r hK hW xi v w initial).mass T:ℝ))=
      Q.push p := by
    funext T
    exact initializedReturnsLaw_cast A R C K j k n t r hK hW xi v w initial T
  rw [he]
  have hc := distance_push Q p nu
  have hr := repeated_return_stationary A R C hC K H L j k n hK hW hB hj hjH hbox
    xi hx0 hx1 hPL hCheeger v hp w hw hgood hn nu hnu hmass U hU hwarm t
  have ht := distance_triangle (Q.push p) (Q.push nu)
    (fun S => RootedWarmStart.law A R j S.val.val)
  exact ht.trans (_root_.add_le_add hc hr)

end
end ContingencyTables.RootedReturnWords

end OAI
