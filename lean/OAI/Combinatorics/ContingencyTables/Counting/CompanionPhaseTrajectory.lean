import OAI.Combinatorics.ContingencyTables.Counting.CompanionBooleanKernel
import Mathlib.Data.List.OfFn

namespace OAI

/-! # The observed Boolean trajectory has the source path law

The finite history stores the visited prefix. Its exact real reference
expectation is the manuscript's list-path expectation, so the row error
controls events involving all empirical observations simultaneously.
-/

namespace ContingencyTables.CompanionPhaseTrajectory

open CommonBasesFPRAS RealKernelApproximation CompanionBooleanPhase
open FirstSuccess ResidualMixture FiniteLawMoments
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {X : Type*}

def historyPrefix {N : ℕ} (a : PathState X N) : List X :=
  List.ofFn (fun i : Fin (a.1.val+1) =>
    a.2 ⟨i.val,lt_of_lt_of_le i.isLt (Nat.succ_le_succ (Nat.le_of_lt_succ a.1.isLt))⟩)

lemma prefix_nonempty {N : ℕ} (a : PathState X N) : historyPrefix a≠[] := by
  simp [historyPrefix]

lemma prefix_last {N : ℕ} (a : PathState X N) :
    (historyPrefix a).getLast (prefix_nonempty a)=pathRead a := by
  unfold historyPrefix
  rw [List.getLast_ofFn_succ]
  apply congrArg a.2
  apply Fin.ext
  rfl

lemma prefix_end {N : ℕ} (a : PathState X N) :
    (historyPrefix a).dropLast++[pathRead a]=historyPrefix a := by
  rw [←prefix_last a]
  exact List.dropLast_append_getLast (prefix_nonempty a)

lemma read_put {N : ℕ} (a : PathState X N) (x : X) : pathRead (pathPut a x)=x := by
  simp [pathRead,pathPut]

lemma position_put {N : ℕ} (a : PathState X N) (x : X) (h : a.1.val<N) :
    (pathPut a x).1.val=a.1.val+1 := by
  simp only [pathPut,nextPosition,min_eq_left (Nat.succ_le_of_lt h)]

lemma prefix_put {N : ℕ} (a : PathState X N) (x : X) (h : a.1.val<N) :
    historyPrefix (pathPut a x)=historyPrefix a++[x] := by
  rcases a with ⟨⟨i,hi⟩,v⟩
  change i<N at h
  have hh : i+1≤N := by omega
  simp only [historyPrefix,pathPut,nextPosition,min_eq_left hh]
  rw [List.ofFn_succ',List.concat_eq_append]
  congr 1
  · apply congrArg List.ofFn
    funext k
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      have hv' : k.val=i+1 := by simpa only [Fin.cast,Fin.castSucc,Fin.castAdd,Fin.castLE] using hv
      exact (Nat.ne_of_lt k.isLt) hv')]
    exact congrArg v (Fin.ext rfl)
  · simp only [List.singleton_inj]
    exact Function.update_self _ _ _

lemma prefix_initial (N : ℕ) (x : X) : historyPrefix (pathInitial N x)=[x] := by
  simp [historyPrefix,pathInitial,List.ofFn_succ]

variable [Fintype X]

private lemma power_succ_left (K : FiniteKernel X X) (n : ℕ) (x z : X) :
    (K.power (n+1)).P x z=∑ y,K.P x y*(K.power n).P y z := by
  induction n generalizing x z with
  | zero => simp [FiniteKernel.power,FiniteKernel.comp,FiniteKernel.identity]
  | succ n ih =>
    change (∑ y,(K.power (n+1)).P x y*K.P y z)=
      ∑ y,K.P x y*(∑ v,(K.power n).P y v*K.P v z)
    simp_rw [ih,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    exact Finset.sum_comm

private lemma power_expectation_succ (K : FiniteKernel X X) (n : ℕ) (x : X) (F : X → ℝ) :
    (∑ z,(K.power (n+1)).P x z*F z)=
      ∑ y,K.P x y*(∑ z,(K.power n).P y z*F z) := by
  simp_rw [power_succ_left,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

omit [Fintype X] in
private lemma lift_expectation {Y Z : Type*} [Fintype Y] [Fintype Z]
    (K : FiniteKernel X Y) (read : Z → X) (put : Z → Y → Z) (a : Z) (F : Z → ℝ) :
    (∑ b,(liftKernel K read put).P a b*F b)=∑ y,K.P (read a) y*F (put a y) := by
  simp only [liftKernel,FiniteKernel.push,mapKernel,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  simp

/-- Before saturation, the finite lifted chain has exactly the usual
list-path expectation, with the observed prefix retained. -/
theorem prefix_expectation (C : FiniteChain X) (N n : ℕ)
    (a : PathState X N) (hn : a.1.val+n≤N) (F : List X → ℝ) :
    (∑ b,((liftKernel C.kernel pathRead pathPut).power n).P a b*F (historyPrefix b))=
      C.pathExpectation n (pathRead a) (fun l => F ((historyPrefix a).dropLast++l)) := by
  induction n generalizing a F with
  | zero =>
    simp only [FiniteKernel.power,FiniteKernel.identity,FiniteChain.pathExpectation,
      ite_mul,one_mul,zero_mul]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,prefix_end]
  | succ n ih =>
    have ha : a.1.val<N := by omega
    rw [power_expectation_succ,lift_expectation]
    change (∑ y,C.P (pathRead a) y*
      (∑ b,((liftKernel C.kernel pathRead pathPut).power n).P (pathPut a y) b*F (historyPrefix b)))=_
    calc
      _ = ∑ y,C.P (pathRead a) y*
          C.pathExpectation n (pathRead (pathPut a y))
            (fun l => F ((historyPrefix (pathPut a y)).dropLast++l)) := by
        apply Finset.sum_congr rfl
        intro y _
        congr 1
        apply ih
        rw [position_put a y ha]
        omega
      _ = C.pathExpectation (n+1) (pathRead a) (fun l => F ((historyPrefix a).dropLast++l)) := by
        simp only [read_put,prefix_put a _ ha,List.dropLast_concat,FiniteChain.pathExpectation]
        apply Finset.sum_congr rfl
        intro y _
        congr 1
        apply congrArg (C.pathExpectation n y)
        funext l
        simpa only [List.append_assoc,List.singleton_append] using
          congrArg (fun xs => F (xs++l)) (prefix_end a).symm

theorem initial_prefix_expectation (C : FiniteChain X) (N : ℕ) (x : X) (F : List X → ℝ) :
    (∑ b,((liftKernel C.kernel pathRead pathPut).power N).P (pathInitial N x) b*F (historyPrefix b))=
      C.pathExpectation N x F := by
  have h := prefix_expectation C N N (pathInitial N x) (by simp [pathInitial]) F
  rw [prefix_initial] at h
  simpa only [List.dropLast_singleton,List.nil_append,pathRead,pathInitial] using h

private lemma event_le_distance {Y : Type*} [Fintype Y] (p q : Y → ℝ)
    (hmass : ∑ y,p y=∑ y,q y) (E : Y → Prop) :
    (∑ y,p y*(if E y then 1 else 0))≤
      (∑ y,q y*(if E y then 1 else 0))+distance p q := by
  have h := distance_event p q hmass (Finset.univ.filter E)
  rw [Finset.sum_filter,Finset.sum_filter] at h
  simp only [mul_ite,mul_one,mul_zero]
  linarith [le_abs_self ((∑ y,if E y then p y else 0)-(∑ y,if E y then q y else 0))]

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Every event of the actual observed Boolean trajectory is bounded by
the source list-path event plus one proved row error per transition. -/
theorem recorded_event_bound (A : Instance I J) (C : ℕ) (hC : 0<C) (K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j≤rationalHeight A C) (xi : ℚ) (hx0 : 0<xi) (hx1 : xi≤1/4)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) (N : ℕ) (S : State A)
    (E : List (State A) → Prop) :
    uniformAverage (fun bits : Fin (N*stepBits A C K j k xi) → Bool =>
      if E (historyPrefix (recordedWalk A C K j k N N hK hW xi v w S bits)) then (1:ℝ) else 0)≤
      (targetChain A j hp w hw).pathExpectation N S (fun l => if E l then 1 else 0)+
        N*((6*(xi:ℝ)+1/(2:ℝ)^k)/2) := by
  let p := pathLaw A C K j k N N hK hW xi v w S
  let q := targetPathMass A j hp w hw N N S
  have hq : ∑ b,q b=1 := by
    have hh := initial_prefix_expectation (targetChain A j hp w hw) N S (fun _ => (1:ℝ))
    simpa only [targetPathMass,q,mul_one,FiniteChain.pathExpectation_const] using hh
  have hpq : (∑ b,(p.mass b:ℝ))=∑ b,q b := by rw [hq]; exact_mod_cast p.total
  have he := event_le_distance (fun b => (p.mass b:ℝ)) q hpq (fun b => E (historyPrefix b))
  have hd := path_distance_bound A C hC K j k hK hW hB hj xi hx0 hx1 hPL hCheeger v hp w hw N N S
  have hword := word_expectation (recordedWalk A C K j k N N hK hW xi v w S)
    (fun b => if E (historyPrefix b) then (1:ℝ) else 0)
  rw [recordedWalk_law] at hword
  change _=∑ b,(p.mass b:ℝ)*(if E (historyPrefix b) then 1 else 0) at hword
  have htarget := initial_prefix_expectation (targetChain A j hp w hw) N S
    (fun l => if E l then (1:ℝ) else 0)
  change (∑ b,q b*(if E (historyPrefix b) then 1 else 0))=_ at htarget
  rw [hword]
  exact he.trans (by rw [htarget]; exact add_le_add_right hd _)

end

end ContingencyTables.CompanionPhaseTrajectory

end OAI
