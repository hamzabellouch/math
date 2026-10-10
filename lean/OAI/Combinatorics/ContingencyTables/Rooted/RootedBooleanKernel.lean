import OAI.Combinatorics.ContingencyTables.Rooted.RootedBooleanPhase
import OAI.Combinatorics.ContingencyTables.Rooted.RootedWarmStart
import OAI.Combinatorics.ContingencyTables.Rooted.RootedConcentration
import OAI.Combinatorics.ContingencyTables.Transport.FiniteLawMoments
import OAI.Combinatorics.ContingencyTables.Transport.FiniteChainSlowdown
import OAI.Combinatorics.ContingencyTables.Transport.RealPathApproximation

namespace OAI

/-! # Selected-root Boolean row law and full-history perturbation -/

namespace ContingencyTables.RootedBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates RootedOracleAcceptance
open CommonBasesFPRAS FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open FiniteLawMoments RealKernelApproximation
open CompanionBooleanPhase (State proposal proposal_mass proposalBits proposal_codes stepBits stepWordEquiv
  slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil)
open scoped BigOperators Classical

noncomputable section

private lemma word_probability {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X]
    [DecidableEq Y] (draw : X → Y) (y : Y) :
    uniformAverage (fun x => if draw x=y then (1:ℝ) else 0)=
      ((mapLaw (uniformLaw (α := X)) draw).mass y:ℝ) := by
  rw [word_expectation draw (fun z => if z=y then (1:ℝ) else 0)]
  simp [expectation]

private lemma independent_decision {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (P : A → Prop) (Q : B → Prop) (R : C → D → Prop)
    [DecidablePred P] [DecidablePred Q] [∀ c d,Decidable (R c d)] :
    uniformAverage (fun z : A×(B×(C×D)) =>
      if P z.1 ∧ Q z.2.1 ∧ R z.2.2.1 z.2.2.2 then (1:ℝ) else 0)=
      uniformAverage (fun a => if P a then (1:ℝ) else 0)*
        uniformAverage (fun b => if Q b then (1:ℝ) else 0)*
        uniformAverage (fun c => uniformAverage (fun d => if R c d then (1:ℝ) else 0)) := by
  have he (z : A×(B×(C×D))) :
      (if P z.1 ∧ Q z.2.1 ∧ R z.2.2.1 z.2.2.2 then (1:ℝ) else 0)=
        (if P z.1 then 1 else 0)*
          ((if Q z.2.1 then 1 else 0)*(if R z.2.2.1 z.2.2.2 then 1 else 0)) := by
    by_cases hp : P z.1 <;> by_cases hq : Q z.2.1 <;>
      by_cases hr : R z.2.2.1 z.2.2.2 <;> simp [hp,hq,hr]
  have hs : (∑ a : A,∑ b : B,∑ c : C,∑ d : D,
      (if P a then (1:ℝ) else 0)*((if Q b then 1 else 0)*(if R c d then 1 else 0)))=
      (∑ a : A,if P a then (1:ℝ) else 0)*(∑ b : B,if Q b then (1:ℝ) else 0)*
        (∑ c : C,∑ d : D,if R c d then (1:ℝ) else 0) := by
    symm
    simp only [Finset.sum_mul,mul_assoc]
    simp only [Finset.mul_sum]
  simp only [he,uniformAverage,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,
    ←Finset.sum_div]
  rw [hs]
  ring

private lemma lazy_probability :
    uniformAverage (fun b : Fin 1 → Bool => if b 0=false then (1:ℝ) else 0)=1/2 := by
  rw [uniformAverage_fin_succ]
  simp only [Fin.cons_zero,uniformAverage_const]
  norm_num [uniformAverage]

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Every nontrivial output probability factors into its lazy bit,
unique neighbor code, and the actual rounded two-oracle acceptance. -/
theorem transition_mass (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi<1)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0<w p q) (S T : State A) (hST : S≠T) :
    ((transitionLaw A R C K j k hK hW xi v w S).mass T:ℝ)=
      if ExchangeAdjacent S.val T.val then
        (1/(2*(2:ℝ)^proposalBits A))*
          uniformAverage (fun b : WeightWord A C K j xi×WeightWord A C K j xi =>
            (rationalThresholdMass k
              (acceptance A R C K j hK hW xi v w S.val T.val b):ℝ))
      else 0 := by
  have hp : uniformAverage (fun b : Fin (proposalBits A) → Bool =>
      if proposal A S b=some T then (1:ℝ) else 0)=
        if ExchangeAdjacent S.val T.val then 1/(2:ℝ)^proposalBits A else 0 := by
    rw [word_probability,proposal_mass]
    split_ifs <;> simp
  have ha (b : WeightWord A C K j xi×WeightWord A C K j xi) :
      uniformAverage (fun coin : Fin k → Bool =>
        if rationalThresholdAccept k
          (acceptance A R C K j hK hW xi v w S.val T.val b) coin then (1:ℝ) else 0)=
        (rationalThresholdMass k
          (acceptance A R C K j hK hW xi v w S.val T.val b):ℝ) := by
    exact rationalThreshold_expectation k _
      (acceptance_bounds A R C hC K j hK hW hB hj xi hx0 hx1 v w hw S.val T.val b).1
      (acceptance_bounds A R C hC K j hK hW hB hj xi hx0 hx1 v w hw S.val T.val b).2
  calc
    _ = uniformAverage (fun bits => if step A R C K j k hK hW xi v w S bits=T then (1:ℝ) else 0) :=
      (word_probability _ T).symm
    _ = uniformAverage (fun b : (Fin 1 → Bool)×((Fin (proposalBits A) → Bool)×
        ((WeightWord A C K j xi×WeightWord A C K j xi)×(Fin k → Bool))) =>
      if b.1 0=false ∧ proposal A S b.2.1=some T ∧
        rationalThresholdAccept k
          (acceptance A R C K j hK hW xi v w S.val T.val b.2.2.1) b.2.2.2
      then (1:ℝ) else 0) := by
        simp_rw [step_eq_iff A R C K j k hK hW xi v w S T hST]
        have he := uniformAverage_equiv (stepWordEquiv A C K j k xi)
          (fun b : (Fin 1 → Bool)×((Fin (proposalBits A) → Bool)×
            ((WeightWord A C K j xi×WeightWord A C K j xi)×(Fin k → Bool))) =>
            if b.1 0=false ∧ proposal A S b.2.1=some T ∧
              rationalThresholdAccept k
                (acceptance A R C K j hK hW xi v w S.val T.val b.2.2.1) b.2.2.2
            then (1:ℝ) else 0)
        convert he using 1
    _ = _ := by
      rw [independent_decision (fun b : Fin 1 → Bool => b 0=false)
        (fun b : Fin (proposalBits A) → Bool => proposal A S b=some T)
        (fun b coin => rationalThresholdAccept k
          (acceptance A R C K j hK hW xi v w S.val T.val b) coin),lazy_probability,hp]
      simp_rw [ha]
      split_ifs <;> ring

/-- The exact target row is the source Metropolis chain, slowed by its
dyadic neighbor-code padding. The stationary distribution is unchanged. -/
def referenceChain (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) : FiniteChain (State A) :=
  metropolisChain pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
    (fun p q => (w p q:ℝ)) (RootedAnnealing.weight A R j)
    (fun p q => by exact_mod_cast hw p q) (RootedAnnealing.weight_positive A R j)

private lemma chain_eq {X : Type*} [Fintype X] (C D : FiniteChain X)
    (hP : C.P=D.P) (hpi : C.π=D.π) : C=D := by
  cases C
  cases D
  dsimp only at hP hpi
  cases hP
  cases hpi
  rfl

/-- The degree completion used to prove the signature and concentration
theorems leaves every state and transition of the literal chain intact. -/
theorem referenceChain_eq_completed (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0<w p q) :
    referenceChain A R j hp w hw=
      metropolisChain pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
        (fun p q => (w p q:ℝ))
        (DegreeCompletion.completeDegree (RootedAnnealing.weight A R j)
          (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length)
        (fun p q => by exact_mod_cast hw p q)
        (DegreeCompletion.completeDegree_positive _ _ (RootedWarmStart.actual_degree A R j).1) := by
  have he (U : State A) :
      chainWeight pairs (fun p q => (w p q:ℝ))
          (DegreeCompletion.completeDegree (RootedAnnealing.weight A R j)
            (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length) U.val=
        chainWeight pairs (fun p q => (w p q:ℝ)) (RootedAnnealing.weight A R j) U.val := by
    simp only [chainWeight,DegreeCompletion.completeDegree,
      U.property.ncard PairedLabels.fresh PairedLabels.cover,ite_true]
  apply chain_eq
  · funext S T
    dsimp only [referenceChain,metropolisChain,FiniteChain.ofMoves]
    simp only [metropolisMove,he]
  · funext S
    dsimp only [referenceChain,metropolisChain,FiniteChain.ofMoves]
    rw [ObservableBounds.chainTotal_completion _ _ _ PairedLabels.fresh PairedLabels.cover,he]

def targetChain (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) : FiniteChain (State A) :=
  FiniteChainSlowdown.slow (referenceChain A R j hp w hw) (slowdown A)
    (by linarith [(slowdown_bounds A hp).1]) (slowdown_bounds A hp).2

theorem target_mass (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (S T : State A) (hST : S≠T) :
    (targetChain A R j hp w hw).P S T=
      if ExchangeAdjacent S.val T.val then
        (1/(2*(2:ℝ)^proposalBits A))*targetAcceptance A R j w S.val T.val else 0 := by
  have hn : (Fintype.card (Labels A):ℝ)≠0 := by exact_mod_cast hp.ne'
  have hs := targetWeight_positive A R j w hw S.val
  have hm : targetAcceptance A R j w S.val T.val=
      min (targetWeight A R j w S.val) (targetWeight A R j w T.val)/targetWeight A R j w S.val := by
    unfold targetAcceptance
    rw [←min_div_div_right hs.le,div_self hs.ne']
  dsimp only [targetChain,FiniteChainSlowdown.slow,referenceChain,metropolisChain,FiniteChain.ofMoves]
  simp only [hST,ite_false,add_zero,metropolisMove,PairedLabels.length]
  by_cases ha : ExchangeAdjacent S.val T.val
  · rw [ite_eq_left ha,ite_eq_left ha]
    simp only [←targetWeight_eq,slowdown,hm]
    field_simp [hn,hs.ne']
  · simp [ha]

private lemma distance_le_off_diagonal {X : Type*} [Fintype X] [DecidableEq X]
    (p q : X → ℝ) (x : X) (hmass : ∑ y,p y=∑ y,q y) :
    distance p q≤∑ y∈Finset.univ.erase x,|p y-q y| := by
  have ht : (∑ y∈Finset.univ.erase x,(p y-q y))+(p x-q x)=0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ x),Finset.sum_sub_distrib,hmass,sub_self]
  have hd : p x-q x= -(∑ y∈Finset.univ.erase x,(p y-q y)) := by linarith
  have hb := Finset.abs_sum_le_sum_abs (fun y => p y-q y) (Finset.univ.erase x)
  have he := Finset.sum_erase_add (Finset.univ : Finset X) (fun y => |p y-q y|)
    (Finset.mem_univ x)
  rw [hd,abs_neg] at he
  unfold distance
  linarith

private lemma average_abs {X : Type*} [Fintype X] (f : X → ℝ) :
    |uniformAverage f|≤uniformAverage (fun x => |f x|) := by
  unfold uniformAverage
  rw [abs_div,abs_of_nonneg (show (0:ℝ)≤Fintype.card X from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs f Finset.univ)
    (Nat.cast_nonneg _)

/-- The complete transition row loses at most half the acceptance error.
The diagonal is controlled by conservation of probability, rather than
an additional independent error assumption. -/
theorem row_distance (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (S : State A) :
    distance (fun T => ((transitionLaw A R C K j k hK hW xi v w S).mass T:ℝ))
      ((targetChain A R j hp w hw).P S)≤(6*(xi:ℝ)+1/(2:ℝ)^k)/2 := by
  let e : ℝ := 6*(xi:ℝ)+1/(2:ℝ)^k
  let a : ℝ := 1/(2*(2:ℝ)^proposalBits A)
  have he : 0≤e := by dsimp only [e]; positivity
  have ha : 0≤a := by dsimp only [a]; positivity
  have hpnt (T : State A) (hST : S≠T) :
      |((transitionLaw A R C K j k hK hW xi v w S).mass T:ℝ)-
        (targetChain A R j hp w hw).P S T|≤
          if ExchangeAdjacent S.val T.val then a*e else 0 := by
    rw [transition_mass A R C hC K j k hK hW hB hj xi hx0
      (by linarith) v w hw S T hST,target_mass A R j hp w hw S T hST]
    by_cases h : ExchangeAdjacent S.val T.val
    · simp only [h,ite_true]
      rw [←mul_sub,abs_mul,abs_of_nonneg ha]
      apply mul_le_mul_of_nonneg_left _ ha
      rw [←uniformAverage_sub_const]
      exact (average_abs _).trans
        (average_acceptance_error A R C hC K j k hK hW hB hj xi hx0 hx1
          hPL hCheeger v w hw S.val T.val)
    · simp [h]
  have hm : (∑ T,((transitionLaw A R C K j k hK hW xi v w S).mass T:ℝ))=
      ∑ T,(targetChain A R j hp w hw).P S T := by
    rw [(targetChain A R j hp w hw).stochastic]
    exact_mod_cast (transitionLaw A R C K j k hK hW xi v w S).total
  have hc : ((Finset.univ.filter (fun T : State A => ExchangeAdjacent S.val T.val)).card:ℝ)≤
      (2:ℝ)^proposalBits A := by
    have hh := proposal_codes A S
    rw [Fintype.card_subtype] at hh
    exact_mod_cast hh
  calc
    _ ≤ ∑ T∈Finset.univ.erase S,
        |((transitionLaw A R C K j k hK hW xi v w S).mass T:ℝ)-
          (targetChain A R j hp w hw).P S T| := distance_le_off_diagonal _ _ S hm
    _ ≤ ∑ T∈Finset.univ.erase S,
        if ExchangeAdjacent S.val T.val then a*e else 0 := by
      apply Finset.sum_le_sum
      intro T hT
      exact hpnt T (Finset.mem_erase.mp hT).1.symm
    _ ≤ ∑ T : State A,if ExchangeAdjacent S.val T.val then a*e else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro T _ _
      split_ifs <;> positivity
    _ = ((Finset.univ.filter (fun T : State A => ExchangeAdjacent S.val T.val)).card:ℝ)*(a*e) := by
      rw [←Finset.sum_filter]
      simp
    _ ≤ (2:ℝ)^proposalBits A*(a*e) := mul_le_mul_of_nonneg_right hc (mul_nonneg ha he)
    _ = e/2 := by dsimp only [a]; field_simp

def pathLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A) :
    RationalLaw (PathState (State A) N) :=
  walkLaw (liftRational (transitionLaw A R C K j k hK hW xi v w)
    (fun a : PathState (State A) N => pathRead a)
    (fun (a : PathState (State A) N) (T : State A) => pathPut a T)) (pathInitial N S) n

def targetPathMass (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (N n : ℕ) (S : State A) :
    PathState (State A) N → ℝ :=
  ((liftKernel (targetChain A R j hp w hw).kernel
    (fun a : PathState (State A) N => pathRead a)
    (fun (a : PathState (State A) N) (T : State A) => pathPut a T)).power n).P (pathInitial N S)

/-- The error controls the whole recorded phase history, not merely its
last state. Every step uses a disjoint fresh oracle/acceptance word. -/
theorem path_distance_bound (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0<C) (K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (N n : ℕ) (S : State A) :
    distance (X := PathState (State A) N)
      (fun b : PathState (State A) N => ((pathLaw A R C K j k N n hK hW xi v w S).mass b:ℝ))
      (targetPathMass A R j hp w hw N n S)≤n*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  unfold pathLaw targetPathMass
  apply walk_distance
  intro a
  apply (lifted_row_distance (transitionLaw A R C K j k hK hW xi v w)
    (targetChain A R j hp w hw).kernel
    (fun a : PathState (State A) N => pathRead a)
    (fun (a : PathState (State A) N) (T : State A) => pathPut a T) a).trans
  exact row_distance A R C hC K j k hK hW hB hj xi hx0 hx1 hPL hCheeger v hp w hw (pathRead a)

/-- The same finite step word records the newly sampled state, so the
history law is physically realized by the concatenated step words. -/
def recordedWalk (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A)
    (bits : Fin (n*stepBits A C K j k xi) → Bool) : PathState (State A) N :=
  wordWalk (fun a b => pathPut a (step A R C K j k hK hW xi v w (pathRead a) b))
    (pathInitial N S) n (oracleWalkWordEquiv n (stepBits A C K j k xi) bits)

theorem recordedWalk_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A) :
    mapLaw (uniformLaw (α := Fin (n*stepBits A C K j k xi) → Bool))
      (recordedWalk A R C K j k N n hK hW xi v w S)=
      walkLaw (liftRational (transitionLaw A R C K j k hK hW xi v w) pathRead pathPut)
        (pathInitial N S) n := by
  unfold recordedWalk
  rw [←map_equiv (oracleWalkWordEquiv n (stepBits A C K j k xi)),uniform_equiv]
  rw [show mapLaw (uniformLaw (α := Fin n → Fin (stepBits A C K j k xi) → Bool))
      (wordWalk (fun a b => pathPut a (step A R C K j k hK hW xi v w (pathRead a) b))
        (pathInitial N S) n)=wordWalkLaw
          (fun a b => pathPut a (step A R C K j k hK hW xi v w (pathRead a) b))
          (pathInitial N S) n from rfl,wordWalkLaw_eq]
  apply congrArg (fun Q => walkLaw Q (pathInitial N S) n)
  funext a
  exact (mapLaw_comp (uniformLaw (α := Fin (stepBits A C K j k xi) → Bool))
    (step A R C K j k hK hW xi v w (pathRead a)) (pathPut a)).symm

end
end ContingencyTables.RootedBooleanPhase

end OAI
