import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhaseOracleError

namespace OAI

/-! # Actual selected-root guarded rational phase update and logarithmic error -/

namespace ContingencyTables.RootedPhaseAccuracy

open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing
open RootedMultiplierUpdate CompanionRationalUpdates RootedPhaseWords
open CompanionPhaseWords (phaseBits Stored)
open TwoLiftStates GridBoundary CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

private lemma indicator_sum {X : Type*} (P : X → Prop) (xs : List X) :
    (xs.map (fun x => if P x then (1:ℝ) else 0)).sum=
      (xs.countP (fun x => decide (P x)):ℝ) := by
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases h : P x <;> simp [h,ih,add_comm]

private lemma count_positive_of_empirical {X : Type*} (P : Set X → Prop)
    (xs : List (Set X))
    (h : 0<empirical (fun S => if P S then (1:ℝ) else 0) xs) :
    0<xs.countP (fun S => decide (P S)) := by
  by_contra hn
  have hz := Nat.eq_zero_of_not_pos hn
  simp only [empirical,indicator_sum,hz,Nat.cast_zero,zero_div] at h
  exact (lt_irrefl (0:ℝ)) h

variable {I J : Type} [Fintype I] [Fintype J]

theorem accurate_counts_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (w : Pair A → Pair A → ℝ) (hw : ∀ p q,0<w p q)
    (eta : ℝ) (heta : eta≤1/4) (xs : List (Set (Labels A×Bool)))
    (hacc : AccuratePhase pairs w (weight A R j) (ratio A R j) eta xs) :
    CountsPositive A xs := by
  have hZ := chainTotal_pos pairs PairedLabels.fresh PairedLabels.cover w
    (weight A R j) (weight_positive A R j) hw
  have hplain : 0<chainMean pairs w (weight A R j) (plainObservable pairs (fun _ => 1)) := by
    rw [plain_probability_mean pairs PairedLabels.fresh PairedLabels.cover]
    exact div_pos (slotTotal_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh) hZ
  have hpemp := AnnealingMultipliers.empirical_positive hplain heta
    (accurate_plain pairs w (weight A R j) (ratio A R j) eta xs hacc).1
  constructor
  · exact count_positive_of_empirical (PlainState pairs) xs hpemp
  · intro p hp q hq hpq
    have hdef : 0<chainMean pairs w (weight A R j) (defectIndicator pairs p q) := by
      rw [defectIndicator_mean pairs PairedLabels.fresh PairedLabels.cover _ _ p q hp hq hpq]
      exact div_pos (mul_pos (hw p q)
        (slotDefect_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh p q hp hq hpq)) hZ
    have hdemp := AnnealingMultipliers.empirical_positive hdef heta
      (accurate_defect pairs w (weight A R j) (ratio A R j) eta xs hacc p q hp hq hpq).1
    exact count_positive_of_empirical (DefectState pairs p q) xs hdemp

theorem observed_ratio_error (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ) (hx0 : 0≤xi) (hx1 : xi≤1/4)
    (v : Grid (I := Fin (dimension A)) K)
    (w : Pair A → Pair A → ℝ) (hw : ∀ p q,0<w p q)
    (eta : ℝ) (he0 : 0≤eta) (he1 : eta≤1/4)
    (states : Fin N → Set (Labels A×Bool))
    (hacc : AccuratePhase pairs w (weight A R j) (ratio A R j) eta (List.ofFn states))
    (bits : Fin (phaseBits A C K j N xi) → Bool)
    (hcalls : accurateCalls A R C K j N hK hW xi v states bits) :
    0<(observedRatio A R C K j N hK hW xi v states bits:ℝ) ∧
      |Real.log ((observedRatio A R C K j N hK hW xi v states bits:ℝ)/
        (slotTotal pairs (weight A R (j+1)) ∅/slotTotal pairs (weight A R j) ∅))|≤
          4*(xi:ℝ)+4*eta := by
  have hcount := (accurate_counts_positive A R j w hw eta he1 (List.ofFn states) hacc).1
  have he := exactObservedRatio_positive A R j N states hcount
  have hb := observedRatio_bounds A R C K j N hK hW xi hx0 hx1 v states bits hcalls
  have ho : 0<(observedRatio A R C K j N hK hW xi v states bits:ℝ) :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) he) hb.1
  have horacle := observedRatio_log_error A R C K j N hK hW xi hx0 hx1 v states hcount bits hcalls
  have hsample := RootedMultiplierUpdate.successful_phase_ratio_log
    A R j w hw eta he0 he1 (List.ofFn states) hacc
  rw [←exactObservedRatio_eq A R j N states] at hsample
  let ratioTotal := slotTotal pairs (weight A R (j+1)) ∅/slotTotal pairs (weight A R j) ∅
  have hR : 0<ratioTotal := div_pos
    (slotTotal_pos pairs _ (weight_positive A R (j+1)) ∅ PairedLabels.fresh)
    (slotTotal_pos pairs _ (weight_positive A R j) ∅ PairedLabels.fresh)
  have hm : (observedRatio A R C K j N hK hW xi v states bits:ℝ)/ratioTotal=
      ((observedRatio A R C K j N hK hW xi v states bits:ℝ)/exactObservedRatio A R j N states)*
        (exactObservedRatio A R j N states/ratioTotal) := by
    field_simp [he.ne',hR.ne']
  refine ⟨ho,?_⟩
  change |Real.log ((observedRatio A R C K j N hK hW xi v states bits:ℝ)/ratioTotal)|≤_
  rw [hm,Real.log_mul (div_ne_zero ho.ne' he.ne') (div_ne_zero he.ne' hR.ne')]
  exact (abs_add_le _ _).trans (_root_.add_le_add horacle hsample)

/-- The actual guarded rational update succeeds on the proved accuracy
events; its stored multipliers are good for the next literal weight. -/
theorem update_success (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ) (hx0 : 0≤xi) (hx1 : xi≤1/4)
    (v : Grid (I := Fin (dimension A)) K) (old : Stored A)
    (hw : ∀ p q,0<old.multiplier p q) (hE : 0<old.estimate)
    (eta : ℝ) (he0 : 0≤eta) (he1 : eta≤1/4)
    (states : Fin N → Set (Labels A×Bool))
    (hacc : AccuratePhase pairs (fun p q => (old.multiplier p q:ℝ))
      (weight A R j) (ratio A R j) eta (List.ofFn states))
    (bits : Fin (phaseBits A C K j N xi) → Bool)
    (hcalls : accurateCalls A R C K j N hK hW xi v states bits) :
    ∃ next,update A R C K j N hK hW xi v old states bits=some next ∧
      (∀ p q,0<next.multiplier p q) ∧ 0<next.estimate ∧
      GoodMultipliers pairs (weight A R (j+1)) (fun p q => (next.multiplier p q:ℝ)) ∧
      |Real.log ((next.estimate:ℝ)/((old.estimate:ℝ)*
        (slotTotal pairs (weight A R (j+1)) ∅/slotTotal pairs (weight A R j) ∅)))|≤
          4*(xi:ℝ)+4*eta := by
  have hwr : ∀ p q,0<(old.multiplier p q:ℝ) := fun p q => by exact_mod_cast hw p q
  have hc := accurate_counts_positive A R j _ hwr eta he1 (List.ofFn states) hacc
  let next : Stored A := ⟨rationalLearn pairs old.multiplier (List.ofFn states),
    old.estimate*observedRatio A R C K j N hK hW xi v states bits⟩
  have hu : update A R C K j N hK hW xi v old states bits=some next := by
    simp only [update,hc,ite_true,next]
  have hnpos : ∀ p q,0<next.multiplier p q := by
    apply checkedUpdate_positive A old.multiplier hw (List.ofFn states)
    simp only [checkedUpdate,hc,ite_true,next]
  have hobs := observed_ratio_error A R C K j N hK hW xi hx0 hx1 v _ hwr eta he0 he1
    states hacc bits hcalls
  have ho : 0<observedRatio A R C K j N hK hW xi v states bits := by exact_mod_cast hobs.1
  have hgood := RootedMultiplierUpdate.successful_phase_learns A R j _ hwr eta he0 he1
    (List.ofFn states) hacc
  have hcast : (fun p q => (next.multiplier p q:ℝ))=
      learnedMultipliers pairs (fun p q => (old.multiplier p q:ℝ)) (List.ofFn states) := by
    funext p q
    exact update_multiplier_cast A R C K j N hK hW xi v old next states bits hu p q
  refine ⟨next,hu,hnpos,mul_pos hE ho,?_,?_⟩
  · rw [hcast]
    exact hgood
  · have hER : (old.estimate:ℝ)≠0 := by exact_mod_cast hE.ne'
    change |Real.log (((old.estimate*observedRatio A R C K j N hK hW xi v states bits:ℚ):ℝ)/_)|≤_
    rw [Rat.cast_mul,mul_div_mul_left _ _ hER]
    exact hobs.2

end
end ContingencyTables.RootedPhaseAccuracy

end OAI
