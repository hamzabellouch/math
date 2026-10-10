import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhaseWords
import OAI.Combinatorics.ContingencyTables.Rooted.RootedMultiplierUpdate
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseOracleError

namespace OAI

/-! # Error of actual selected-root calls in a rational phase update -/

namespace ContingencyTables.RootedPhaseWords

open CompanionFactorialApplication CompanionOracleDensity RootedWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS FiniteIndependentAverages GridBoundary TwoLiftStates
open CompanionPhaseWords (phaseBits phaseWordEquiv average_ext_instances failure_of_success
  independent_pair_failure independent_reindex_failure)
open CompanionWeightOracle (WeightWord)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

def accurateCalls (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool))
    (bits : Fin (phaseBits A C K j N xi) → Bool) : Prop :=
  ∀ i,accurateCall A R C K j hK hW xi v (states i) (phaseWordEquiv A C K j N xi bits i).1 ∧
    accurateCall A R C K (j+1) hK hW xi v (states i) (phaseWordEquiv A C K j N xi bits i).2

lemma accurateCall_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool)) :
    uniformAverage (fun bits : WeightWord A C K j xi =>
      if ¬accurateCall A R C K j hK hW xi v S bits then (1:ℝ) else 0) ≤ (xi:ℝ) := by
  have hs := evaluate_success A R C hC K hK hW hB j hj xi hx0 hx1 hPL hCheeger v S
  exact @failure_of_success (WeightWord A C K j xi) inferInstance inferInstance
    (accurateCall A R C K j hK hW xi v S) (xi:ℝ) hs

lemma pairedCalls_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool)) :
    uniformAverage (fun bits : WeightWord A C K j xi × WeightWord A C K (j+1) xi =>
      if ¬(accurateCall A R C K j hK hW xi v S bits.1 ∧
        accurateCall A R C K (j+1) hK hW xi v S bits.2) then (1:ℝ) else 0) ≤ (xi:ℝ)+(xi:ℝ) := by
  have hS := accurateCall_failure A R C hC K j hK hW hB (by omega) xi hx0 hx1 hPL hCheeger v S
  have hT := accurateCall_failure A R C hC K (j+1) hK hW hB hj xi hx0 hx1 hPL hCheeger v S
  exact @independent_pair_failure (WeightWord A C K j xi) (WeightWord A C K (j+1) xi)
    inferInstance inferInstance inferInstance inferInstance
    (accurateCall A R C K j hK hW xi v S) (accurateCall A R C K (j+1) hK hW xi v S)
    (xi:ℝ) (xi:ℝ) hS hT

/-- The calls use independent actual finite words even for a fixed,
arbitrary sequence of observed states. No sampling assumption on that
sequence is required for this oracle-error estimate. -/
theorem accurateCalls_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool)) :
    uniformAverage (fun bits : Fin (phaseBits A C K j N xi) → Bool =>
      if ¬accurateCalls A R C K j N hK hW xi v states bits then (1:ℝ) else 0) ≤
        2*(N:ℝ)*(xi:ℝ) := by
  let X := WeightWord A C K j xi × WeightWord A C K (j+1) xi
  let Y := Fin (phaseBits A C K j N xi) → Bool
  let good (i : Fin N) (b : X) :=
    accurateCall A R C K j hK hW xi v (states i) b.1 ∧
      accurateCall A R C K (j+1) hK hW xi v (states i) b.2
  have hbad (i : Fin N) : uniformAverage (fun b : X => if ¬good i b then (1:ℝ) else 0) ≤
      (xi:ℝ)+(xi:ℝ) := by
    exact pairedCalls_failure A R C hC K j hK hW hB hj xi hx0 hx1 hPL hCheeger v (states i)
  have he := @independent_reindex_failure X Y inferInstance inferInstance inferInstance N
      (phaseWordEquiv A C K j N xi) good
  have hfun : (fun bits : Y =>
      if ¬accurateCalls A R C K j N hK hW xi v states bits then (1:ℝ) else 0)=
      (fun bits : Y => if ¬(∀ i,good i (phaseWordEquiv A C K j N xi bits i)) then (1:ℝ) else 0) := by
    funext bits
    have hi : accurateCalls A R C K j N hK hW xi v states bits ↔
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
def exactObservedRatio (A : Instance I J) (R : RootedCompletion.Selection A.T) (j N : ℕ)
    (states : Fin N → Set (Labels A×Bool)) : ℝ :=
  (∑ i,plainObservable pairs (RootedMultiplierUpdate.ratio A R j) (states i))/
    plainCount A (List.ofFn states)

private lemma indicator_list_sum_real {X : Type*} (P : X → Prop) (l : List X) :
    (l.map (fun x => if P x then (1:ℝ) else 0)).sum=(l.countP (fun x => decide (P x)):ℝ) := by
  induction l with
  | nil => simp
  | cons x l ih => by_cases hx : P x <;> simp [hx,ih,add_comm]

lemma exactObservedRatio_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (j N : ℕ)
    (states : Fin N → Set (Labels A×Bool)) :
    exactObservedRatio A R j N states=
      empiricalRatio pairs (RootedMultiplierUpdate.ratio A R j) (List.ofFn states) := by
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

lemma observedTerm_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ) (hx0 : 0 ≤ xi) (hx1 : xi ≤ 1/4)
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi × WeightWord A C K (j+1) xi)
    (hcall : accurateCall A R C K j hK hW xi v S bits.1 ∧
      accurateCall A R C K (j+1) hK hW xi v S bits.2) :
    Real.exp (-4*(xi:ℝ))*plainObservable pairs (RootedMultiplierUpdate.ratio A R j) S ≤
      (observedTerm A R C K j hK hW xi v S bits:ℝ) ∧
      (observedTerm A R C K j hK hW xi v S bits:ℝ) ≤
        Real.exp (4*(xi:ℝ))*plainObservable pairs (RootedMultiplierUpdate.ratio A R j) S := by
  by_cases hp : PlainState pairs S
  · simp only [observedTerm,plainObservable,hp,ite_true,Rat.cast_div,
      RootedMultiplierUpdate.ratio]
    exact ratio_exponential_bounds (RootedAnnealing.weight_positive A R j S)
      (RootedAnnealing.weight_positive A R (j+1) S) (by exact_mod_cast hx0)
      (by
        have h4 : (4:ℝ)*(xi:ℝ) ≤ 1 := by
          exact_mod_cast (show (4:ℚ)*xi ≤ 1 by linarith)
        linarith) hcall.1 hcall.2
  · simp only [observedTerm,plainObservable,hp,ite_false,Rat.cast_zero,mul_zero,le_refl,and_self]

lemma exactObservedRatio_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (j N : ℕ)
    (states : Fin N → Set (Labels A×Bool)) (hc : 0 < plainCount A (List.ofFn states)) :
    0 < exactObservedRatio A R j N states := by
  obtain ⟨S,hS,hplain⟩ := List.countP_pos_iff.mp hc
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hS
  have hpi : PlainState pairs (states i) := by
    rw [hi]
    exact of_decide_eq_true hplain
  have hterm : 0 < plainObservable pairs (RootedMultiplierUpdate.ratio A R j) (states i) := by
    rw [plainObservable,ite_eq_left hpi]
    exact lt_of_lt_of_le (by norm_num) (RootedMultiplierUpdate.ratio_bounds A R j (states i)).1
  unfold exactObservedRatio
  apply div_pos _ (by exact_mod_cast hc)
  apply hterm.trans_le
  apply Finset.single_le_sum _ (Finset.mem_univ i)
  intro k _
  by_cases hk : PlainState pairs (states k)
  · rw [plainObservable,ite_eq_left hk]
    exact le_trans (by norm_num) (RootedMultiplierUpdate.ratio_bounds A R j (states k)).1
  · simp only [plainObservable,hk,ite_false,le_refl]

/-- Relative errors of all fresh calls remain bounded after averaging
the state ratios. The number of observations does not enlarge this
deterministic multiplicative error. -/
theorem observedRatio_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ) (hx0 : 0 ≤ xi) (hx1 : xi ≤ 1/4)
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool))
    (bits : Fin (phaseBits A C K j N xi) → Bool)
    (hg : accurateCalls A R C K j N hK hW xi v states bits) :
    Real.exp (-4*(xi:ℝ))*exactObservedRatio A R j N states ≤
      (observedRatio A R C K j N hK hW xi v states bits:ℝ) ∧
      (observedRatio A R C K j N hK hW xi v states bits:ℝ) ≤
        Real.exp (4*(xi:ℝ))*exactObservedRatio A R j N states := by
  have hb (i : Fin N) := observedTerm_bounds A R C K j hK hW xi hx0 hx1 v (states i)
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

theorem observedRatio_log_error (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ) (hx0 : 0 ≤ xi) (hx1 : xi ≤ 1/4)
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool))
    (hc : 0 < plainCount A (List.ofFn states))
    (bits : Fin (phaseBits A C K j N xi) → Bool)
    (hg : accurateCalls A R C K j N hK hW xi v states bits) :
    |Real.log ((observedRatio A R C K j N hK hW xi v states bits:ℝ)/
      exactObservedRatio A R j N states)| ≤ 4*(xi:ℝ) := by
  have he := exactObservedRatio_positive A R j N states hc
  have hb := observedRatio_bounds A R C K j N hK hW xi hx0 hx1 v states bits hg
  have ho := lt_of_lt_of_le (mul_pos (Real.exp_pos _) he) hb.1
  have hl := (le_div_iff₀ he).mpr hb.1
  have hu := (div_le_iff₀ he).mpr hb.2
  have hlogl := Real.log_le_log (Real.exp_pos _) hl
  have hlogu := Real.log_le_log (div_pos ho he) hu
  rw [Real.log_exp] at hlogl hlogu
  exact abs_le.mpr ⟨by linarith, hlogu⟩

end
end ContingencyTables.RootedPhaseWords

end OAI
