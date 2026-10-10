import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseWords
import OAI.Combinatorics.ContingencyTables.Transport.FiniteIndependentFailures

namespace OAI

/-! # Error contributed by the actual fresh weight calls in a phase -/

namespace ContingencyTables.CompanionPhaseWords

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS FiniteIndependentAverages GridBoundary TwoLiftStates
open scoped BigOperators Classical

noncomputable section

lemma average_ext_instances {X : Type*} (s t : Fintype X) (f g : X → ℝ)
    (h : ∀ x,f x=g x) : @uniformAverage X s f=@uniformAverage X t g := by
  cases Subsingleton.elim s t
  exact congrArg (@uniformAverage X s) (funext h)

lemma failure_of_success {X : Type*} [Fintype X] [Nonempty X]
    (P : X → Prop) (delta : ℝ)
    (h : 1-delta ≤ uniformAverage (fun x => if P x then (1:ℝ) else 0)) :
    uniformAverage (fun x => if ¬P x then (1:ℝ) else 0) ≤ delta := by
  have hp (x : X) : (if P x then (1:ℝ) else 0)+(if ¬P x then 1 else 0)=1 := by
    by_cases hx : P x <;> simp [hx]
  have he := uniformAverage_add (fun x => if P x then (1:ℝ) else 0)
    (fun x => if ¬P x then (1:ℝ) else 0)
  simp_rw [hp] at he
  rw [uniformAverage_const] at he
  linarith

lemma independent_pair_failure {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (P : X → Prop) (Q : Y → Prop)
    (a b : ℝ) (hP : uniformAverage (fun x => if ¬P x then (1:ℝ) else 0) ≤ a)
    (hQ : uniformAverage (fun y => if ¬Q y then (1:ℝ) else 0) ≤ b) :
    uniformAverage (fun xy : X×Y => if ¬(P xy.1 ∧ Q xy.2) then (1:ℝ) else 0) ≤ a+b := by
  have hfst : uniformAverage (fun xy : X×Y => if ¬P xy.1 then (1:ℝ) else 0)=
      uniformAverage (fun x => if ¬P x then (1:ℝ) else 0) := by
    calc
      _ = uniformAverage (fun x : X => uniformAverage (fun _y : Y => if ¬P x then (1:ℝ) else 0)) :=
        @uniformAverage_prod X Y _ _ (fun xy : X×Y => if ¬P xy.1 then (1:ℝ) else 0)
      _ = _ := by simp_rw [uniformAverage_const]
  have hsnd : uniformAverage (fun xy : X×Y => if ¬Q xy.2 then (1:ℝ) else 0)=
      uniformAverage (fun y => if ¬Q y then (1:ℝ) else 0) := by
    calc
      _ = uniformAverage (fun _x : X => uniformAverage (fun y : Y => if ¬Q y then (1:ℝ) else 0)) :=
        @uniformAverage_prod X Y _ _ (fun xy : X×Y => if ¬Q xy.2 then (1:ℝ) else 0)
      _ = _ := uniformAverage_const _
  calc
    _ ≤ uniformAverage (fun xy : X×Y =>
        (if ¬P xy.1 then (1:ℝ) else 0)+(if ¬Q xy.2 then (1:ℝ) else 0)) := by
      apply uniformAverage_mono
      intro xy
      by_cases hp : P xy.1 <;> by_cases hq : Q xy.2 <;> simp [hp,hq]
    _ = uniformAverage (fun x => if ¬P x then (1:ℝ) else 0)+
        uniformAverage (fun y => if ¬Q y then (1:ℝ) else 0) := by
      rw [uniformAverage_add,hfst,hsnd]
    _ ≤ a+b := add_le_add hP hQ

lemma independent_reindex_failure {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X]
    (N : ℕ) (e : Y ≃ (Fin N → X)) (P : Fin N → X → Prop) :
    uniformAverage (fun y : Y => if ¬(∀ i,P i (e y i)) then (1:ℝ) else 0) ≤
      ∑ i : Fin N,uniformAverage (fun x : X => if ¬P i x then (1:ℝ) else 0) := by
  let bad (i : Fin N) (x : X) := ¬P i x
  have he := uniformAverage_equiv e
    (fun xs : Fin N → X => if ∃ i,bad i (xs i) then (1:ℝ) else 0)
  have hb : uniformAverage (fun xs : Fin N → X => if ∃ i,bad i (xs i) then (1:ℝ) else 0) ≤
      ∑ i : Fin N,uniformAverage (fun x : X => if bad i x then (1:ℝ) else 0) := by
    convert independent_union_failure bad using 1
    all_goals
      congr 1 <;> try exact Subsingleton.elim _ _
    · funext xs
      by_cases h : ∃ i,bad i (xs i) <;> simp [h]
    · funext i
      congr 1
      funext x
      by_cases h : bad i x <;> simp [h]
  simpa only [bad,not_forall] using he.trans_le hb

variable {I J : Type*} [Fintype I] [Fintype J]

def accurateCalls (A : Instance I J) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool))
    (bits : Fin (phaseBits A C K j N xi) → Bool) : Prop :=
  ∀ i,accurateCall A C K j hK hW xi v (states i) (phaseWordEquiv A C K j N xi bits i).1 ∧
    accurateCall A C K (j+1) hK hW xi v (states i) (phaseWordEquiv A C K j N xi bits i).2

lemma accurateCall_failure (A : Instance I J) (C : ℕ) (hC : 0 < C) (K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool)) :
    uniformAverage (fun bits : WeightWord A C K j xi =>
      if ¬accurateCall A C K j hK hW xi v S bits then (1:ℝ) else 0) ≤ (xi:ℝ) := by
  have hs := evaluate_success A C hC K hK hW hB j hj xi hx0 hx1 hPL hCheeger v S
  exact @failure_of_success (WeightWord A C K j xi) inferInstance inferInstance
    (accurateCall A C K j hK hW xi v S) (xi:ℝ) hs

lemma pairedCalls_failure (A : Instance I J) (C : ℕ) (hC : 0 < C) (K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool)) :
    uniformAverage (fun bits : WeightWord A C K j xi × WeightWord A C K (j+1) xi =>
      if ¬(accurateCall A C K j hK hW xi v S bits.1 ∧
        accurateCall A C K (j+1) hK hW xi v S bits.2) then (1:ℝ) else 0) ≤ (xi:ℝ)+(xi:ℝ) := by
  have hS := accurateCall_failure A C hC K j hK hW hB (by omega) xi hx0 hx1 hPL hCheeger v S
  have hT := accurateCall_failure A C hC K (j+1) hK hW hB hj xi hx0 hx1 hPL hCheeger v S
  exact @independent_pair_failure (WeightWord A C K j xi) (WeightWord A C K (j+1) xi)
    inferInstance inferInstance inferInstance inferInstance
    (accurateCall A C K j hK hW xi v S) (accurateCall A C K (j+1) hK hW xi v S)
    (xi:ℝ) (xi:ℝ) hS hT

/-- The calls use independent actual finite words even for a fixed,
arbitrary sequence of observed states. No sampling assumption on that
sequence is required for this oracle-error estimate. -/
theorem accurateCalls_failure (A : Instance I J) (C : ℕ) (hC : 0 < C) (K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool)) :
    uniformAverage (fun bits : Fin (phaseBits A C K j N xi) → Bool =>
      if ¬accurateCalls A C K j N hK hW xi v states bits then (1:ℝ) else 0) ≤
        2*(N:ℝ)*(xi:ℝ) := by
  let X := WeightWord A C K j xi × WeightWord A C K (j+1) xi
  let Y := Fin (phaseBits A C K j N xi) → Bool
  let good (i : Fin N) (b : X) :=
    accurateCall A C K j hK hW xi v (states i) b.1 ∧
      accurateCall A C K (j+1) hK hW xi v (states i) b.2
  have hbad (i : Fin N) : uniformAverage (fun b : X => if ¬good i b then (1:ℝ) else 0) ≤
      (xi:ℝ)+(xi:ℝ) := by
    exact pairedCalls_failure A C hC K j hK hW hB hj xi hx0 hx1 hPL hCheeger v (states i)
  have he := @independent_reindex_failure X Y inferInstance inferInstance inferInstance N
      (phaseWordEquiv A C K j N xi) good
  have hfun : (fun bits : Y =>
      if ¬accurateCalls A C K j N hK hW xi v states bits then (1:ℝ) else 0)=
      (fun bits : Y => if ¬(∀ i,good i (phaseWordEquiv A C K j N xi bits i)) then (1:ℝ) else 0) := by
    funext bits
    have hi : accurateCalls A C K j N hK hW xi v states bits ↔
        ∀ i,good i (phaseWordEquiv A C K j N xi bits i) := Iff.rfl
    by_cases h : ∀ i,good i (phaseWordEquiv A C K j N xi bits i)
    · simp [hi,h]
    · simp [hi,h]
  rw [hfun]
  calc
    _ ≤ ∑ i : Fin N,uniformAverage (fun b : X => if ¬good i b then (1:ℝ) else 0) :=
      by
        convert he using 1
        · apply average_ext_instances
          intro bits
          by_cases hh : ∀ i,good i (phaseWordEquiv A C K j N xi bits i) <;> simp [hh]
        · apply Finset.sum_congr rfl
          intro i _
          apply average_ext_instances
          intro b
          by_cases hh : good i b <;> simp [hh]
    _ ≤ ∑ _ : Fin N,((xi:ℝ)+(xi:ℝ)) := Finset.sum_le_sum (fun i _ => hbad i)
    _ = 2*(N:ℝ)*(xi:ℝ) := by simp; ring

/-- The exact empirical ratio written as the plain-state sum divided
by its integer plain-state population. -/
def exactObservedRatio (A : Instance I J) (j N : ℕ)
    (states : Fin N → Set (Labels A×Bool)) : ℝ :=
  (∑ i,plainObservable pairs (CompanionMultiplierUpdate.ratio A j) (states i))/
    plainCount A (List.ofFn states)

private lemma indicator_list_sum_real {X : Type*} (P : X → Prop) (l : List X) :
    (l.map (fun x => if P x then (1:ℝ) else 0)).sum=(l.countP (fun x => decide (P x)):ℝ) := by
  induction l with
  | nil => simp
  | cons x l ih => by_cases hx : P x <;> simp [hx,ih,add_comm]

lemma exactObservedRatio_eq (A : Instance I J) (j N : ℕ)
    (states : Fin N → Set (Labels A×Bool)) :
    exactObservedRatio A j N states=
      empiricalRatio pairs (CompanionMultiplierUpdate.ratio A j) (List.ofFn states) := by
  by_cases hN : N=0
  · subst N
    simp [exactObservedRatio,empiricalRatio,empirical,plainCount]
  · have hNR : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN
    unfold exactObservedRatio empiricalRatio empirical
    unfold plainObservable
    rw [indicator_list_sum_real]
    simp only [List.map_ofFn,List.sum_ofFn,List.length_ofFn,plainCount]
    exact (div_div_div_cancel_right₀ hNR _ _).symm

private lemma ratio_exponential_bounds {u v uh vh e : ℝ}
    (hu : 0 < u) (hv : 0 < v) (he0 : 0 ≤ e) (he1 : e ≤ 1/4)
    (huh : (1-e)*u ≤ uh ∧ uh ≤ (1+e)*u)
    (hvh : (1-e)*v ≤ vh ∧ vh ≤ (1+e)*v) :
    Real.exp (-4*e)*(v/u) ≤ vh/uh ∧ vh/uh ≤ Real.exp (4*e)*(v/u) := by
  have huh0 := AnnealingMultipliers.empirical_positive hu he1 huh.1
  have hr := AnnealingMultipliers.relative_ratio hv hu he0 he1 hvh huh
  have hid : vh*u/(uh*v)=(vh/uh)/(v/u) := by
    field_simp [hu.ne',hv.ne',huh0.ne']
  rw [hid] at hr
  have hlo : Real.exp (-4*e) ≤ (vh/uh)/(v/u) := by
    calc
      _ ≤ Real.exp (Real.log ((vh/uh)/(v/u))) :=
        Real.exp_le_exp.mpr (by linarith [(abs_le.mp hr.2.2.2).1])
      _ = _ := Real.exp_log hr.1
  have hhi : (vh/uh)/(v/u) ≤ Real.exp (4*e) := by
    calc
      _ = Real.exp (Real.log ((vh/uh)/(v/u))) := (Real.exp_log hr.1).symm
      _ ≤ _ := Real.exp_le_exp.mpr (abs_le.mp hr.2.2.2).2
  exact ⟨(le_div_iff₀ (div_pos hv hu)).mp hlo,(div_le_iff₀ (div_pos hv hu)).mp hhi⟩

lemma observedTerm_bounds (A : Instance I J) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ) (hx0 : 0 ≤ xi) (hx1 : xi ≤ 1/4)
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi × WeightWord A C K (j+1) xi)
    (hcall : accurateCall A C K j hK hW xi v S bits.1 ∧
      accurateCall A C K (j+1) hK hW xi v S bits.2) :
    Real.exp (-4*(xi:ℝ))*plainObservable pairs (CompanionMultiplierUpdate.ratio A j) S ≤
      (observedTerm A C K j hK hW xi v S bits:ℝ) ∧
      (observedTerm A C K j hK hW xi v S bits:ℝ) ≤
        Real.exp (4*(xi:ℝ))*plainObservable pairs (CompanionMultiplierUpdate.ratio A j) S := by
  by_cases hp : PlainState pairs S
  · simp only [observedTerm,plainObservable,hp,ite_true,Rat.cast_div,
      CompanionMultiplierUpdate.ratio]
    exact ratio_exponential_bounds (CompanionAnnealing.weight_positive A j S)
      (CompanionAnnealing.weight_positive A (j+1) S) (by exact_mod_cast hx0)
      (by
        have h4 : (4:ℝ)*(xi:ℝ) ≤ 1 := by
          exact_mod_cast (show (4:ℚ)*xi ≤ 1 by linarith)
        linarith) hcall.1 hcall.2
  · simp only [observedTerm,plainObservable,hp,ite_false,Rat.cast_zero,mul_zero,le_refl,and_self]

lemma exactObservedRatio_positive (A : Instance I J) (j N : ℕ)
    (states : Fin N → Set (Labels A×Bool)) (hc : 0 < plainCount A (List.ofFn states)) :
    0 < exactObservedRatio A j N states := by
  obtain ⟨S,hS,hplain⟩ := List.countP_pos_iff.mp hc
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hS
  have hpi : PlainState pairs (states i) := by
    rw [hi]
    exact of_decide_eq_true hplain
  have hterm : 0 < plainObservable pairs (CompanionMultiplierUpdate.ratio A j) (states i) := by
    rw [plainObservable,ite_eq_left hpi]
    exact lt_of_lt_of_le (by norm_num) (CompanionMultiplierUpdate.ratio_bounds A j (states i)).1
  unfold exactObservedRatio
  apply div_pos _ (by exact_mod_cast hc)
  apply hterm.trans_le
  apply Finset.single_le_sum _ (Finset.mem_univ i)
  intro k _
  by_cases hk : PlainState pairs (states k)
  · rw [plainObservable,ite_eq_left hk]
    exact le_trans (by norm_num) (CompanionMultiplierUpdate.ratio_bounds A j (states k)).1
  · simp only [plainObservable,hk,ite_false,le_refl]

/-- Relative errors of all fresh calls remain bounded after averaging
the state ratios. The number of observations does not enlarge this
deterministic multiplicative error. -/
theorem observedRatio_bounds (A : Instance I J) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ) (hx0 : 0 ≤ xi) (hx1 : xi ≤ 1/4)
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool))
    (bits : Fin (phaseBits A C K j N xi) → Bool)
    (hg : accurateCalls A C K j N hK hW xi v states bits) :
    Real.exp (-4*(xi:ℝ))*exactObservedRatio A j N states ≤
      (observedRatio A C K j N hK hW xi v states bits:ℝ) ∧
      (observedRatio A C K j N hK hW xi v states bits:ℝ) ≤
        Real.exp (4*(xi:ℝ))*exactObservedRatio A j N states := by
  have hb (i : Fin N) := observedTerm_bounds A C K j hK hW xi hx0 hx1 v (states i)
    (phaseWordEquiv A C K j N xi bits i) (hg i)
  simp only [observedRatio,exactObservedRatio,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast]
  constructor
  · rw [←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hb i).1)
  · rw [←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hb i).2)

theorem observedRatio_log_error (A : Instance I J) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ) (hx0 : 0 ≤ xi) (hx1 : xi ≤ 1/4)
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool))
    (hc : 0 < plainCount A (List.ofFn states))
    (bits : Fin (phaseBits A C K j N xi) → Bool)
    (hg : accurateCalls A C K j N hK hW xi v states bits) :
    |Real.log ((observedRatio A C K j N hK hW xi v states bits:ℝ)/
      exactObservedRatio A j N states)| ≤ 4*(xi:ℝ) := by
  have he := exactObservedRatio_positive A j N states hc
  have hb := observedRatio_bounds A C K j N hK hW xi hx0 hx1 v states bits hg
  have ho := lt_of_lt_of_le (mul_pos (Real.exp_pos _) he) hb.1
  have hl := (le_div_iff₀ he).mpr hb.1
  have hu := (div_le_iff₀ he).mpr hb.2
  have hlogl := Real.log_le_log (Real.exp_pos _) hl
  have hlogu := Real.log_le_log (div_pos ho he) hu
  rw [Real.log_exp] at hlogl hlogu
  exact abs_le.mpr ⟨by linarith, hlogu⟩

end

end ContingencyTables.CompanionPhaseWords

end OAI
