import OAI.Combinatorics.ContingencyTables.Counting.CompanionTargetTrace
import OAI.Combinatorics.ContingencyTables.Transport.FiniteLawMoments

namespace OAI

/-! # The implemented capped return on a warm input law

The output kernel comes from the actual bounded Boolean word. Its error
against the literal trace is bounded using the cap loss and the proved
joint-path approximation, averaged under the incoming warm law.
-/

namespace ContingencyTables.CompanionWarmReturn

open CommonBasesFPRAS ResidualMixture FirstSuccess FiniteLawMoments RealKernelApproximation
open CompanionFactorialApplication CompanionBooleanPhase CompanionOracleDensity
open CompanionWeightOracle CompanionRationalUpdates CompanionTraceWords
open CompanionCappedReturn CompanionTargetTrace CompanionAnnealing CompanionWarmStart
open CompanionConcentration TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

private lemma weighted_error {Y : Type*} [Fintype Y]
    (nu f g loss : Y → ℝ) (delta e : ℝ) (hnu : ∀ y,0≤nu y)
    (hmass : ∑ y,nu y≤1) (he : 0≤e)
    (hpoint : ∀ y,f y≤g y+loss y+e) (hloss : ∑ y,nu y*loss y≤delta) :
    (∑ y,nu y*f y)≤(∑ y,nu y*g y)+delta+e := by
  have h := Finset.sum_le_sum (fun y (_ : y∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint y) (hnu y))
  have hm := mul_le_mul_of_nonneg_right hmass he
  simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,one_mul] at h hm
  linarith

private lemma push_observation {X Y : Type*} [Fintype X] [Fintype Y]
    (K : FiniteKernel X Y) (nu : X → ℝ) (g : Y → ℝ) :
    (∑ y,K.push nu y*g y)=∑ x,nu x*(∑ y,K.P x y*g y) := by
  simp only [FiniteKernel.push,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

private theorem distance_of_events {Y : Type*} [Fintype Y]
    (p q : Y → ℝ) (delta : ℝ) (hmass : ∑ y,p y=∑ y,q y)
    (hevent : ∀ E : Y → Prop,(∑ y,p y*eventIndicator (E y))≤
      (∑ y,q y*eventIndicator (E y))+delta) : distance p q≤delta := by
  let E : Y → Prop := fun y => 0≤p y-q y
  have hzero : (∑ y,(p y-q y))=0 := by
    rw [Finset.sum_sub_distrib,hmass,sub_self]
  have hpoint (y : Y) : |p y-q y|=
      2*((p y-q y)*eventIndicator (E y))-(p y-q y) := by
    by_cases h : 0≤p y-q y
    · simp only [E,eventIndicator,h,ite_true,abs_of_nonneg h,mul_one]
      ring
    · simp only [E,eventIndicator,h,ite_false,abs_of_neg (lt_of_not_ge h),mul_zero]
      ring
  have hsum : (∑ y,|p y-q y|)=2*(∑ y,(p y-q y)*eventIndicator (E y)) := by
    simp only [hpoint,Finset.sum_sub_distrib,←Finset.mul_sum,hzero,sub_zero]
  have hh := hevent E
  simp only [sub_mul,Finset.sum_sub_distrib] at hsum
  unfold distance
  rw [hsum]
  linarith

variable {I J : Type} [Fintype I] [Fintype J]

def returnLaw (A : Instance I J) (C K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A))) : RationalLaw (PlainIndex (pairs : List (Pair A))) :=
  mapLaw (uniformLaw (α := Fin ((n+1)*stepBits A C K j k xi) → Bool))
    (returnWordDefault A C K j k n hK hW xi v w S)

def returnKernel (A : Instance I J) (C K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) :
    FiniteKernel (PlainIndex (pairs : List (Pair A))) (PlainIndex (pairs : List (Pair A))) :=
  rationalKernel (returnLaw A C K j k n hK hW xi v w)

private lemma return_observation (A : Instance I J) (C K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A))) (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    (∑ T,(returnKernel A C K j k n hK hW xi v w).P S T*eventIndicator (E T))=
      uniformAverage (fun bits : Fin ((n+1)*stepBits A C K j k xi) → Bool =>
        eventIndicator (E (returnWordDefault A C K j k n hK hW xi v w S bits))) := by
  exact (word_expectation (returnWordDefault A C K j k n hK hW xi v w S)
    (fun T => eventIndicator (E T))).symm

theorem warm_cap_loss (A : Instance I J) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A j) (fun p q => (w p q:ℝ)))
    (n : ℕ) (hn : 0<n) (nu : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hnu : ∀ S,0≤nu S) (U : ℝ) (hU : 0≤U)
    (hwarm : ∀ S,nu S≤U*law A j S.val.val) :
    (∑ S,nu S*(1-∑ T,(targetChain A j hp w hw).cappedTrace (plainPredicate pairs)
      (targetKilled A j hp w hw) n S T))≤(5*(Fintype.card (Labels A):ℝ)^2*U)/(n:ℝ) := by
  let := plainIndex_nonempty (pairs : List (Pair A)) PairedLabels.fresh PairedLabels.cover
  have hwar : ∀ S,nu S≤U*((targetChain A j hp w hw).traceChain (plainPredicate pairs)
      (targetKilled A j hp w hw) (targetKilled_matches A j hp w hw)).π S := by
    intro S
    have hs := hwarm S
    rw [←actualTrace_pi A j hp w hw S] at hs
    simpa only [CompanionTargetTrace.actualTrace] using hs
  have hl := (targetChain A j hp w hw).cappedTrace_warm_loss (plainPredicate pairs)
    (targetKilled A j hp w hw) (targetKilled_matches A j hp w hw) n U nu hnu hwar
  have hpR : (0:ℝ)<Fintype.card (Labels A) := by exact_mod_cast hp
  have hd : (0:ℝ)<5*(Fintype.card (Labels A):ℝ)^2 := by positivity
  have hm := insideMass_lower A j hp w hw hgood
  have hb : U/(targetChain A j hp w hw).insideMass (plainPredicate pairs)≤
      5*(Fintype.card (Labels A):ℝ)^2*U := by
    calc
      _ ≤ U/(1/(5*(Fintype.card (Labels A):ℝ)^2)) :=
        div_le_div_of_nonneg_left hU (one_div_pos.mpr hd) hm
      _ = _ := by simp only [one_div,div_inv_eq_mul]; ring
  apply (le_div_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)).mpr
  have hc := hl.trans hb
  simpa only [mul_comm] using hc

private lemma returnKernel_stochastic (A : Instance I J) (C K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A))) :
    ∑ T,(returnKernel A C K j k n hK hW xi v w).P S T=1 := by
  change (∑ T,((returnLaw A C K j k n hK hW xi v w S).mass T:ℝ))=1
  exact_mod_cast (returnLaw A C K j k n hK hW xi v w S).total

private theorem weighted_return_event (A : Instance I J) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A j) (fun p q => (w p q:ℝ)))
    (hn : 0<n) (nu : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hnu : ∀ S,0≤nu S) (hmass : ∑ S,nu S≤1) (U : ℝ) (hU : 0≤U)
    (hwarm : ∀ S,nu S≤U*law A j S.val.val)
    (E : PlainIndex (pairs : List (Pair A)) → Prop) :
    (∑ S,nu S*(∑ T,(returnKernel A C K j k n hK hW xi v w).P S T*eventIndicator (E T)))≤
      (∑ S,nu S*(∑ T,(CompanionTargetTrace.actualTrace A j hp w hw).kernel.P S T*
        eventIndicator (E T)))+
        (5*(Fintype.card (Labels A):ℝ)^2*U)/(n:ℝ)+
          ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  let f : PlainIndex (pairs : List (Pair A)) → ℝ := fun S =>
    ∑ T,(returnKernel A C K j k n hK hW xi v w).P S T*eventIndicator (E T)
  let g : PlainIndex (pairs : List (Pair A)) → ℝ := fun S =>
    ∑ T,(CompanionTargetTrace.actualTrace A j hp w hw).kernel.P S T*eventIndicator (E T)
  let loss : PlainIndex (pairs : List (Pair A)) → ℝ := fun S =>
    1-∑ T,(targetChain A j hp w hw).cappedTrace (plainPredicate pairs)
      (targetKilled A j hp w hw) n S T
  let err : ℝ := ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2)
  have herr : 0≤err := by dsimp only [err]; positivity
  have hpoint (S) : f S≤g S+loss S+err := by
      dsimp only [f,g,loss,err]
      rw [return_observation]
      exact returnWordDefault_event A C hC K j k n hK hW hB hj xi hx0 hx1
        hPL hCheeger v hp w hw S E
  have hcap := warm_cap_loss A j hp w hw hgood n hn nu hnu U hU hwarm
  have hsum := @weighted_error (PlainIndex (pairs : List (Pair A))) inferInstance
    nu f g loss ((5*(Fintype.card (Labels A):ℝ)^2*U)/(n:ℝ)) err
    hnu hmass herr hpoint hcap
  exact hsum

/-- This is the law of the implemented Boolean return, compared to the
literal trace on the same incoming warm distribution. -/
theorem warm_return_distance (A : Instance I J) (C : ℕ) (hC : 0<C) (K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A j) (fun p q => (w p q:ℝ)))
    (hn : 0<n) (nu : PlainIndex (pairs : List (Pair A)) → ℝ)
    (hnu : ∀ S,0≤nu S) (hmass : ∑ S,nu S≤1) (U : ℝ) (hU : 0≤U)
    (hwarm : ∀ S,nu S≤U*law A j S.val.val) :
    distance ((returnKernel A C K j k n hK hW xi v w).push nu)
      ((CompanionTargetTrace.actualTrace A j hp w hw).kernel.push nu)≤
        (5*(Fintype.card (Labels A):ℝ)^2*U)/(n:ℝ)+
          ((n+1:ℕ):ℝ)*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  apply distance_of_events
  · rw [FiniteKernel.push_mass,FiniteKernel.push_mass]
    simp only [returnKernel_stochastic,FiniteChain.kernel,FiniteChain.stochastic,mul_one]
  · intro E
    rw [push_observation,push_observation]
    have he := weighted_return_event A C hC K j k n hK hW hB hj xi hx0 hx1 hPL hCheeger
      v hp w hw hgood hn nu hnu hmass U hU hwarm E
    simpa only [add_assoc] using he

end
end ContingencyTables.CompanionWarmReturn

end OAI
