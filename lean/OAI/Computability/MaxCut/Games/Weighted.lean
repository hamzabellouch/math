import Mathlib
import OAI.Computability.MaxCut.Games.WeightRounding
import OAI.Computability.MaxCut.Games.CanonicalAddress
import OAI.Computability.MaxCut.Games.Probability

namespace OAI

namespace MaxCutGames.Reduction.WeightedSource

open scoped BigOperators
open WeightRounding

structure RationalSource (Eqn : Type) where
  occurrences : Nat
  positive : 0 < occurrences
  equation : Fin occurrences → Eqn
  weight : Fin occurrences → ℚ
  nonnegative : ∀ i, 0 ≤ weight i
  normalized : ∑ i, weight i = 1

namespace RationalSource

variable {Eqn : Type} (S : RationalSource Eqn)

def denominator : Nat := ∏ i, (S.weight i).den

theorem denominator_positive : 0 < S.denominator := by
  exact Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => (S.weight i).den_ne_zero)

theorem den_dvd_denominator (i : Fin S.occurrences) :
    (S.weight i).den ∣ S.denominator := by
  exact Finset.dvd_prod_of_mem (fun j => (S.weight j).den) (Finset.mem_univ i)

def numerator (i : Fin S.occurrences) : Nat :=
  (S.weight i).num.toNat * (S.denominator / (S.weight i).den)

theorem numerator_cast (i : Fin S.occurrences) :
    (S.numerator i : ℚ) = S.weight i * S.denominator := by
  have hn : (((S.weight i).num.toNat : Nat) : ℚ) = ((S.weight i).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (S.nonnegative i))
  have hd : ((S.weight i).den : ℚ) ≠ 0 := by
    exact_mod_cast (S.weight i).den_ne_zero
  have hdiv : ((S.denominator / (S.weight i).den : Nat) : ℚ) * (S.weight i).den = S.denominator := by
    exact_mod_cast Nat.div_mul_cancel (S.den_dvd_denominator i)
  have hnum : ((S.weight i).num : ℚ) = S.weight i * (S.weight i).den :=
    (div_eq_iff hd).mp (S.weight i).num_div_den
  rw [numerator, Nat.cast_mul, hn, hnum]
  calc
    S.weight i * (S.weight i).den * ↑(S.denominator / (S.weight i).den) =
        S.weight i * (↑(S.denominator / (S.weight i).den) * (S.weight i).den) := by ring
    _ = _ := by rw [hdiv]

/-- Exact rational-to-integer conversion, not an approximation. -/
theorem weight_eq_ratio (i : Fin S.occurrences) :
    S.weight i = (S.numerator i : ℚ) / S.denominator := by
  have hq : (S.denominator : ℚ) ≠ 0 := by exact_mod_cast S.denominator_positive.ne'
  rw [S.numerator_cast]
  field_simp

def numerators : List Nat := List.ofFn S.numerator

theorem length_numerators : S.numerators.length = S.occurrences := by
  simp [numerators]

theorem sum_numerators : S.numerators.sum = S.denominator := by
  have h : (∑ i, (S.numerator i : ℚ)) = (S.denominator : ℚ) := by
    simp_rw [S.numerator_cast]
    rw [← Finset.sum_mul, S.normalized, one_mul]
  simpa only [numerators, List.sum_ofFn] using (show (∑ i, S.numerator i) = S.denominator by exact_mod_cast h)

def equationAt (i : Nat) : Eqn :=
  if h : i < S.occurrences then S.equation ⟨i, h⟩ else S.equation ⟨0, S.positive⟩

@[simp] theorem equationAt_fin (i : Fin S.occurrences) :
    S.equationAt i.val = S.equation i := by simp [equationAt, i.isLt]

def roundedEquations (D : Nat) : List Eqn :=
  (uniformSource D S.denominator S.numerators).map S.equationAt

theorem roundedEquations_length (D : Nat) : (S.roundedEquations D).length = D := by
  simp only [roundedEquations, List.length_map]
  exact length_uniformSource D S.denominator S.numerators S.denominator_positive S.sum_numerators

theorem roundedEquations_nonempty (D : Nat) (hD : 0 < D) : S.roundedEquations D ≠ [] := by
  intro h
  have hl := S.roundedEquations_length D
  rw [h] at hl
  simp at hl
  omega

/-- Rounding copies complete equation records without altering any of their slots. -/
theorem roundedEquations_origin (D : Nat) (e : Eqn) (he : e ∈ S.roundedEquations D) :
    ∃ i : Fin S.occurrences, e = S.equation i := by
  obtain ⟨j, _, hj⟩ := List.mem_map.mp he
  rw [← hj]
  unfold equationAt
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

def weightedValue (accept : Eqn → Bool) : ℚ :=
  ∑ i, if accept (S.equation i) then S.weight i else 0

def roundedValue (D : Nat) (accept : Eqn → Bool) : ℚ :=
  ((S.roundedEquations D).filter accept).length / (D : ℚ)

end RationalSource

theorem selectedSum_ofFn {n : Nat} (p : Fin n → Nat) (keep : Nat → Bool) :
    selectedSum (List.ofFn p) keep = ∑ i, if keep i.val then p i else 0 := by
  induction n generalizing keep with
  | zero => simp [selectedSum]
  | succ n ih =>
    rw [List.ofFn_succ, selectedSum, Fin.sum_univ_succ]
    rw [ih]
    rfl

namespace RationalSource

variable {Eqn : Type} (S : RationalSource Eqn)

theorem selectedMass_cast (accept : Eqn → Bool) :
    (selectedSum S.numerators (fun i => accept (S.equationAt i)) : ℚ) =
      S.weightedValue accept * S.denominator := by
  rw [numerators, selectedSum_ofFn, Nat.cast_sum]
  simp only [S.equationAt_fin]
  rw [weightedValue, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  cases accept (S.equation i) <;> simp [S.numerator_cast]

theorem roundedValue_bounds (D : Nat) (hD : 0 < D) (accept : Eqn → Bool) :
    S.weightedValue accept - S.occurrences / (D : ℚ) ≤ S.roundedValue D accept ∧
    S.roundedValue D accept ≤ S.weightedValue accept + S.occurrences / (D : ℚ) := by
  have herr := uniformSource_error D S.denominator S.numerators
    (fun i => accept (S.equationAt i)) S.denominator_positive
  have hc : ((S.roundedEquations D).filter accept).length =
      ((uniformSource D S.denominator S.numerators).filter (fun i => accept (S.equationAt i))).length := by
    simp [roundedEquations, List.filter_map, Function.comp_def]
  have hupper : (((S.roundedEquations D).filter accept).length : ℚ) * S.denominator ≤
      D * (selectedSum S.numerators (fun i => accept (S.equationAt i)) : ℚ) +
        S.occurrences * (S.denominator : ℚ) := by
    rw [hc]
    exact_mod_cast (S.length_numerators ▸ herr.1)
  have hlower : (D : ℚ) * (selectedSum S.numerators (fun i => accept (S.equationAt i)) : ℚ) ≤
      ((S.roundedEquations D).filter accept).length * (S.denominator : ℚ) +
        S.occurrences * (S.denominator : ℚ) := by
    rw [hc]
    exact_mod_cast (S.length_numerators ▸ herr.2)
  rw [S.selectedMass_cast] at hupper hlower
  have hq : (0 : ℚ) < S.denominator := by exact_mod_cast S.denominator_positive
  have hd : (0 : ℚ) < D := by exact_mod_cast hD
  have hu : (((S.roundedEquations D).filter accept).length : ℚ) ≤
      D * S.weightedValue accept + S.occurrences := by
    apply le_of_mul_le_mul_right (a := (S.denominator : ℚ)) _ hq
    nlinarith [hupper]
  have hl : (D : ℚ) * S.weightedValue accept ≤
      ((S.roundedEquations D).filter accept).length + (S.occurrences : ℚ) := by
    apply le_of_mul_le_mul_right (a := (S.denominator : ℚ)) _ hq
    nlinarith [hlower]
  unfold roundedValue
  constructor
  · apply (le_div_iff₀ hd).mpr
    calc
      (S.weightedValue accept - S.occurrences / (D : ℚ)) * D =
          D * S.weightedValue accept - S.occurrences := by field_simp
      _ ≤ _ := by linarith
  · apply (div_le_iff₀ hd).mpr
    calc
      _ ≤ D * S.weightedValue accept + S.occurrences := hu
      _ = (S.weightedValue accept + S.occurrences / (D : ℚ)) * D := by field_simp

/-- `ceil(4m/γ)` computed from the exact numerator and denominator of `γ`. -/
def roundingDenominator (γ : ℚ) : Nat :=
  targetDenominator S.occurrences γ.num.toNat γ.den

theorem roundingDenominator_positive (γ : ℚ) (hγ : 0 < γ) :
    0 < S.roundingDenominator γ := by
  exact targetDenominator_positive _ _ _ S.positive
    (Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr hγ)) γ.den_pos

theorem roundingDenominator_budget (γ : ℚ) (hγ : 0 < γ) :
    S.occurrences / (S.roundingDenominator γ : ℚ) ≤ γ / 4 := by
  have hn : 0 < γ.num.toNat := Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr hγ)
  have h := targetDenominator_error_budget S.occurrences γ.num.toNat γ.den hn
  have hncast : (γ.num.toNat : ℚ) = (γ.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hγ.le)
  have hnum : (γ.num.toNat : ℚ) = γ * γ.den := by
    rw [hncast]
    exact (div_eq_iff (by exact_mod_cast γ.den_ne_zero)).mp γ.num_div_den
  have hcast : (4 : ℚ) * S.occurrences * γ.den ≤
      S.roundingDenominator γ * (γ.num.toNat : ℚ) := by exact_mod_cast h
  rw [hnum] at hcast
  have hb : (0 : ℚ) < γ.den := by exact_mod_cast γ.den_pos
  have hd : (0 : ℚ) < S.roundingDenominator γ := by
    exact_mod_cast S.roundingDenominator_positive γ hγ
  apply (div_le_iff₀ hd).mpr
  have ht : (4 : ℚ) * S.occurrences ≤ S.roundingDenominator γ * γ := by
    apply le_of_mul_le_mul_right (a := (γ.den : ℚ)) _ hb
    nlinarith [hcast]
  nlinarith

theorem roundingDenominator_size (γ : ℚ) (hγ : 0 < γ) :
    S.roundingDenominator γ ≤ 4 * γ.den * S.occurrences :=
  targetDenominator_size _ _ _ (Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr hγ))

theorem completeness_transport (γ ξ : ℚ) (hγ : 0 < γ) (hξ : ξ ≤ γ / 4)
    (accept : Eqn → Bool) (hsource : 1 - ξ ≤ S.weightedValue accept) :
    1 - γ ≤ S.roundedValue (S.roundingDenominator γ) accept := by
  have h := (S.roundedValue_bounds _ (S.roundingDenominator_positive γ hγ) accept).1
  have hb := S.roundingDenominator_budget γ hγ
  linarith

theorem soundness_transport (γ ξ : ℚ) (hγ : 0 < γ) (hγsmall : γ ≤ 1 / 8)
    (hξ : ξ ≤ 1 / 16) (accept : Eqn → Bool)
    (hsource : S.weightedValue accept ≤ (1 + ξ) / 2) :
    S.roundedValue (S.roundingDenominator γ) accept ≤ 3 / 4 := by
  have h := (S.roundedValue_bounds _ (S.roundingDenominator_positive γ hγ) accept).2
  have hb := S.roundingDenominator_budget γ hγ
  linarith

theorem roundedEquations_for_nonempty (γ : ℚ) (hγ : 0 < γ) :
    S.roundedEquations (S.roundingDenominator γ) ≠ [] :=
  S.roundedEquations_nonempty _ (S.roundingDenominator_positive γ hγ)

end RationalSource

variable {Name : Type} (S : RationalSource (CloneGap.Equation Name))

theorem e3lin_completeness (γ ξ : ℚ) (hγ : 0 < γ) (hξ : ξ ≤ γ / 4)
    (hsource : ∃ g : Name → Bool,
      1 - ξ ≤ S.weightedValue (fun e => CloneGap.satisfied e g)) :
    ∃ g : Name → Bool,
      (1 - γ) * (S.roundedEquations (S.roundingDenominator γ)).length ≤
        (((S.roundedEquations (S.roundingDenominator γ)).filter
          (fun e => CloneGap.satisfied e g)).length : ℚ) := by
  obtain ⟨g, hg⟩ := hsource
  refine ⟨g, ?_⟩
  have h := S.completeness_transport γ ξ hγ hξ (fun e => CloneGap.satisfied e g) hg
  have hd : (0 : ℚ) < S.roundingDenominator γ := by
    exact_mod_cast S.roundingDenominator_positive γ hγ
  unfold RationalSource.roundedValue at h
  have hc := (le_div_iff₀ hd).mp h
  simpa only [S.roundedEquations_length] using hc

theorem e3lin_soundness (γ ξ : ℚ) (hγ : 0 < γ) (hγsmall : γ ≤ 1 / 8)
    (hξ : ξ ≤ 1 / 16)
    (hsource : ∀ g : Name → Bool,
      S.weightedValue (fun e => CloneGap.satisfied e g) ≤ (1 + ξ) / 2) :
    ∀ g : Name → Bool,
      4 * ((S.roundedEquations (S.roundingDenominator γ)).filter
        (fun e => CloneGap.satisfied e g)).length ≤
      3 * (S.roundedEquations (S.roundingDenominator γ)).length := by
  intro g
  have h := S.soundness_transport γ ξ hγ hγsmall hξ
    (fun e => CloneGap.satisfied e g) (hsource g)
  have hd : (0 : ℚ) < S.roundingDenominator γ := by
    exact_mod_cast S.roundingDenominator_positive γ hγ
  unfold RationalSource.roundedValue at h
  have hc := (div_le_iff₀ hd).mp h
  rw [S.roundedEquations_length]
  have hc' : (4 : ℚ) * ((S.roundedEquations (S.roundingDenominator γ)).filter
      (fun e => CloneGap.satisfied e g)).length ≤ 3 * S.roundingDenominator γ := by
    linarith
  exact_mod_cast hc'

end MaxCutGames.Reduction.WeightedSource

namespace MaxCutGames.Reduction.Preprocessing

open ActualSource WeightedSource

def rounded {n : Nat} (W : RationalSource (CloneGap.Equation (Fin n)))
    (γ : ℚ) (hγ : 0 < γ) : Source :=
  Source.ofList (W.roundedEquations (W.roundingDenominator γ))
    (W.roundedEquations_for_nonempty γ hγ)

theorem rounded_failure_add_value {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ : ℚ) (hγ : 0 < γ)
    (A : Fin n → Bool) :
    (rounded W γ hγ).failure A + W.roundedValue (W.roundingDenominator γ)
      (fun e => CloneGap.satisfied e A) = 1 := by
  have h := SourceProbability.failure_add_satisfaction (rounded W γ hγ) A
  simpa [rounded, Source.sourceList, Source.ofList,
    RationalSource.roundedEquations_length, RationalSource.roundedValue,
    List.countP_eq_length_filter] using h

theorem rounded_complete {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hξ : ξ ≤ γ / 4)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A)) :
    ∃ A : Fin (rounded W γ hγ).«variables» → Bool, (rounded W γ hγ).failure A ≤ γ := by
  obtain ⟨A, hA⟩ := hsource
  refine ⟨A, ?_⟩
  have ht := W.completeness_transport γ ξ hγ hξ (fun e => CloneGap.satisfied e A) hA
  have he := rounded_failure_add_value W γ hγ A
  linarith

theorem rounded_sound {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hγsmall : γ ≤ 1 / 8) (hξ : ξ ≤ 1 / 16)
    (hsource : ∀ A : Fin n → Bool,
      W.weightedValue (fun e => CloneGap.satisfied e A) ≤ (1 + ξ) / 2) :
    ∀ A : Fin (rounded W γ hγ).«variables» → Bool,
      (1 / 4 : ℚ) ≤ (rounded W γ hγ).failure A := by
  intro A
  have ht := W.soundness_transport γ ξ hγ hγsmall hξ
    (fun e => CloneGap.satisfied e A) (hsource A)
  have he := rounded_failure_add_value W γ hγ A
  linarith

def uniformSource {n : Nat} (W : RationalSource (CloneGap.Equation (Fin n)))
    (γ : ℚ) (hγ : 0 < γ) : Source := FiniteSource.cloned (rounded W γ hγ)

theorem cloned_failure_eq (S : Source) (A : Fin S.«variables» → Bool) :
    (FiniteSource.cloned S).failure
      (fun z => A ((FiniteSource.nameEquiv S).symm z).1) = S.failure A := by
  have hc := SourceProbability.failure_add_satisfaction (FiniteSource.cloned S)
    (fun z => A ((FiniteSource.nameEquiv S).symm z).1)
  have hs := SourceProbability.failure_add_satisfaction S A
  erw [FiniteSource.cloned_completeness_count S A, FiniteSource.cloned_length S] at hc
  simp only [Nat.cast_mul] at hc
  have hn : (S.occurrences : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt S.nonempty
  have hd : (CloneGap.distinctTriples.length : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt FiniteSource.distinctTriples_nonempty
  have hratio :
      ((S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ) *
        (CloneGap.distinctTriples.length : ℚ)) /
        ((S.occurrences : ℚ) * (CloneGap.distinctTriples.length : ℚ)) =
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ) / S.occurrences := by
    field_simp [hn, hd]
  rw [hratio] at hc
  linarith

theorem uniformSource_complete {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hξ : ξ ≤ γ / 4)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A)) :
    ∃ A : Fin (uniformSource W γ hγ).«variables» → Bool,
      (uniformSource W γ hγ).failure A ≤ γ := by
  obtain ⟨A, hA⟩ := rounded_complete W γ ξ hγ hξ hsource
  refine ⟨fun z => A ((FiniteSource.nameEquiv (rounded W γ hγ)).symm z).1, ?_⟩
  change (FiniteSource.cloned (rounded W γ hγ)).failure _ ≤ γ
  exact (cloned_failure_eq (rounded W γ hγ) A).trans_le hA

theorem uniformSource_distinct {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ : ℚ) (hγ : 0 < γ) :
    (uniformSource W γ hγ).DistinctNames := FiniteSource.cloned_distinct _

theorem uniformSource_sound {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hγsmall : γ ≤ 1 / 8) (hξ : ξ ≤ 1 / 16)
    (hsource : ∀ A : Fin n → Bool,
      W.weightedValue (fun e => CloneGap.satisfied e A) ≤ (1 + ξ) / 2) :
    ∀ A : Fin (uniformSource W γ hγ).«variables» → Bool,
      (1 / 64 : ℚ) ≤ (uniformSource W γ hγ).failure A := by
  intro A
  have hr := rounded_sound W γ ξ hγ hγsmall hξ hsource
  have hgap : ∀ B : Fin (rounded W γ hγ).«variables» → Bool,
      (rounded W γ hγ).sourceList.length ≤
      4 * (rounded W γ hγ).sourceList.countP (fun e => !CloneGap.satisfied e B) := by
    intro B
    exact (SourceProbability.quarter_gap_iff _ B).mp (hr B)
  have hc := FiniteSource.cloned_gap (rounded W γ hγ) hgap A
  change (uniformSource W γ hγ).sourceList.length ≤
    64 * (uniformSource W γ hγ).sourceList.countP (fun e => !CloneGap.satisfied e A) at hc
  rw [SourceProbability.Source_failure_eq_count]
  have hn : (0 : ℚ) < (uniformSource W γ hγ).occurrences := by
    exact_mod_cast (uniformSource W γ hγ).nonempty
  apply (le_div_iff₀ hn).mpr
  rw [Source.sourceList_length] at hc
  have hc' : ((uniformSource W γ hγ).occurrences : ℚ) ≤
      64 * ((uniformSource W γ hγ).sourceList.countP
        (fun e => !CloneGap.satisfied e A) : ℚ) := by exact_mod_cast hc
  linarith

end MaxCutGames.Reduction.Preprocessing

namespace MaxCutGames.Reduction.OuterCompleteness

open ActualSource WeightedSource
open MaxCutGames.Foundations.Target
open MaxCutGames.Integration

/-- Completeness for the actual output after rounding and finite cloning. -/
theorem weighted_completeAt {n s d : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hξ : ξ ≤ γ / 4) (k : Nat) (g : SplitGadget s d)
    (error : RationalError)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A))
    (hbudget : (k : ℚ) * γ + g.stabilityError / 2 ≤ GapSemantics.errorValue error) :
    CompleteAt error
      (ActualGame.outputInstance (Preprocessing.uniformSource W γ hγ) k g) := by
  obtain ⟨A, hA⟩ := Preprocessing.uniformSource_complete W γ ξ hγ hξ hsource
  apply ActualCompleteness.actual_completeAt _ k g A error
  have hm := mul_le_mul_of_nonneg_left hA (show (0 : ℚ) ≤ k by positivity)
  linarith

def sourceError (error : RationalError) (k : Nat) : ℚ :=
  FinalParameters.gamma (GapSemantics.errorValue error) k

theorem sourceError_pos (error : RationalError) {k : Nat} (hk : 0 < k) :
    0 < sourceError error k :=
  (FinalParameters.gamma_bounds (GapSemantics.errorValue_pos error)
    (GapSemantics.errorValue_lt_half error) hk).1

theorem weighted_completeAt_of_parameters {n s d : Nat}
    (error : RationalError) (W : RationalSource (CloneGap.Equation (Fin n)))
    (k : Nat) (hk : 0 < k) (ξ : ℚ)
    (hξ : ξ ≤ sourceError error k / 4) (g : SplitGadget s d)
    (hstable : g.stabilityError ≤ GapSemantics.errorValue error / 2)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A)) :
    CompleteAt error
      (ActualGame.outputInstance
        (Preprocessing.uniformSource W (sourceError error k) (sourceError_pos error hk)) k g) := by
  apply weighted_completeAt W (sourceError error k) ξ (sourceError_pos error hk)
    hξ k g error hsource
  calc
    (k : ℚ) * sourceError error k + g.stabilityError / 2 ≤
        (k : ℚ) * sourceError error k + (GapSemantics.errorValue error / 2) / 2 := by
      linarith
    _ = GapSemantics.errorValue error / 2 := FinalParameters.completeness_budget hk
    _ ≤ GapSemantics.errorValue error := by
      have h := GapSemantics.errorValue_pos error
      linarith

theorem weighted_explicit_completeAt_of_parameters {n s d : Nat}
    (error : RationalError) (W : RationalSource (CloneGap.Equation (Fin n)))
    (k : Nat) (hk : 0 < k) (ξ : ℚ)
    (hξ : ξ ≤ sourceError error k / 4) (g : SplitGadget s d)
    (en : NoiseEnumeration g)
    (hstable : g.stabilityError ≤ GapSemantics.errorValue error / 2)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A)) :
    CompleteAt error
      (ActualGame.outputInstanceWithEnumeration
        (Preprocessing.uniformSource W (sourceError error k) (sourceError_pos error hk))
        k g en) := by
  apply (ActualGame.completeAt_outputInstanceWithEnumeration_iff error _ k g en).mpr
  exact weighted_completeAt_of_parameters error W k hk ξ hξ g hstable hsource

end MaxCutGames.Reduction.OuterCompleteness

namespace MaxCutGames.Reduction.UniformReduction

open ActualSource
open MaxCutGames.Integration
open MaxCutGames.Foundations.Target

variable {n s d : Nat}

def rawSource (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) : Source :=
  Source.ofList es hne

def source (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) : Source :=
  FiniteSource.cloned (rawSource es hne)

/-- All proof-only numerical parameters and the correcting function are absent
    from the runtime input of this map. -/
def output (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) : Instance (2 ^ s) :=
  TableReduction.output (source es hne) k T

def satisfaction (es : List (CloneGap.Equation (Fin n))) (A : Fin n → Bool) : ℚ :=
  (es.countP (fun e => CloneGap.satisfied e A) : ℚ) / es.length

theorem source_variables (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (source es hne).«variables» = n * 48 := rfl

theorem source_occurrences (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (source es hne).occurrences = es.length * CloneGap.distinctTriples.length := by
  exact FiniteSource.cloned_length (rawSource es hne)

theorem source_occurrences_le (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (source es hne).occurrences ≤ 110592 * es.length := by
  have hd : CloneGap.distinctTriples.length ≤ 110592 := by
    exact Nat.le_trans (List.length_filter_le _ CloneGap.triples)
      (by simp [CloneGap.length_triples])
  rw [source_occurrences]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left es.length hd

theorem source_distinct (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (source es hne).DistinctNames := FiniteSource.cloned_distinct (rawSource es hne)

theorem output_constraint_count (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (output es hne k T).constraints.length =
      (es.length * CloneGap.distinctTriples.length) ^ k *
        2 ^ ((2 * k + 1) * (s + d + 1)) * T.vectors.length := by
  unfold output TableReduction.output
  erw [ActualGame.outputInstanceWithEnumeration_length]
  simp only [TableReduction.tableEnumeration, source_occurrences, Explicit.edgeCount]
  erw [List.length_finRange]

theorem output_vertex_count (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (output es hne k T).vertices =
      2 * (ActualGame.explicitBodies (source es hne) k s d).length := rfl

def liftAssignment (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (A : Fin n → Bool) : Fin (source es hne).«variables» → Bool :=
  fun z => A ((FiniteSource.nameEquiv (rawSource es hne)).symm z).1

theorem source_failure_preserved (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (A : Fin n → Bool) :
    (source es hne).failure (liftAssignment es hne A) = (rawSource es hne).failure A :=
  Preprocessing.cloned_failure_eq (rawSource es hne) A

theorem raw_failure_add_satisfaction (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (A : Fin n → Bool) :
    (rawSource es hne).failure A + satisfaction es A = 1 := by
  have h := SourceProbability.failure_add_satisfaction (rawSource es hne) A
  have hl : (rawSource es hne).sourceList = es := Source.sourceList_ofList es hne
  have ho : (rawSource es hne).occurrences = es.length := rfl
  rw [hl, ho] at h
  exact h

theorem source_complete (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (ξ : ℚ) (hsource : ∃ A : Fin n → Bool, 1 - ξ ≤ satisfaction es A) :
    ∃ A : Fin (source es hne).«variables» → Bool, (source es hne).failure A ≤ ξ := by
  obtain ⟨A, hA⟩ := hsource
  refine ⟨liftAssignment es hne A, ?_⟩
  rw [source_failure_preserved]
  have hsum := raw_failure_add_satisfaction es hne A
  linarith

/-- The original uniform `((1+ξ)/2)` satisfaction bound supplies exactly the
    quarter-gap premise needed by the cloning theorem. -/
theorem raw_quarter_count_gap (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (ξ : ℚ) (hξ : ξ ≤ 1 / 2)
    (hsource : ∀ A : Fin n → Bool, satisfaction es A ≤ (1 + ξ) / 2) :
    ∀ A : Fin (rawSource es hne).«variables» → Bool,
      (rawSource es hne).sourceList.length ≤
        4 * (rawSource es hne).sourceList.countP (fun e => !CloneGap.satisfied e A) := by
  intro A
  apply (SourceProbability.quarter_gap_iff (rawSource es hne) A).mp
  have hsum := raw_failure_add_satisfaction es hne A
  have hs := hsource A
  linarith

theorem source_sound (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (ξ : ℚ) (hξ : ξ ≤ 1 / 2)
    (hsource : ∀ A : Fin n → Bool, satisfaction es A ≤ (1 + ξ) / 2) :
    ∀ A : Fin (source es hne).«variables» → Bool,
      (1 / 64 : ℚ) ≤ (source es hne).failure A := by
  intro A
  have hgap := raw_quarter_count_gap es hne ξ hξ hsource
  have hc := FiniteSource.cloned_gap (rawSource es hne) hgap A
  change (source es hne).sourceList.length ≤
    64 * (source es hne).sourceList.countP (fun e => !CloneGap.satisfied e A) at hc
  rw [SourceProbability.Source_failure_eq_count]
  have hn : (0 : ℚ) < (source es hne).occurrences := by
    exact_mod_cast (source es hne).nonempty
  apply (le_div_iff₀ hn).mpr
  rw [Source.sourceList_length] at hc
  have hc' : ((source es hne).occurrences : ℚ) ≤
      64 * ((source es hne).sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) := by
    exact_mod_cast hc
  linarith

theorem sourceGame_sound (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (ξ : ℚ) (hξ : ξ ≤ 1 / 2)
    (hsource : ∀ A : Fin n → Bool, satisfaction es A ≤ (1 + ξ) / 2) :
    (IncidenceProbability.FoundationBridge.sourceGame (source es hne)).value ≤
      (191 : ℝ) / 192 := by
  have h := IncidenceProbability.FoundationBridge.source_value_le_one_sub_gap_third
    (source es hne) (source_distinct es hne) (1 / 64 : ℝ) (fun A => by
      have hrat := source_sound es hne ξ hξ hsource A
      have hr : ((1 / 64 : ℚ) : ℝ) ≤ ((source es hne).failure A : ℝ) := by
        exact_mod_cast hrat
      norm_num at hr ⊢
      exact hr)
  norm_num at h ⊢
  exact h

theorem completeAt_of_parameters (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (error : RationalError) (k : Nat) (hk : 0 < k) (ξ : ℚ)
    (hξ : ξ ≤ FinalParameters.gamma (GapSemantics.errorValue error) k)
    (T : NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c)
    (hstable : (T.gadget f hf).stabilityError ≤ GapSemantics.errorValue error / 2)
    (hsource : ∃ A : Fin n → Bool, 1 - ξ ≤ satisfaction es A) :
    CompleteAt error (output es hne k T) := by
  obtain ⟨A, hA⟩ := source_complete es hne ξ hsource
  apply (TableReduction.completeAt_output_iff error (source es hne) k T f hf).mpr
  apply ActualCompleteness.actual_completeAt (source es hne) k (T.gadget f hf) A error
  have hm := mul_le_mul_of_nonneg_left (hA.trans hξ) (show (0 : ℚ) ≤ k by positivity)
  calc
    (k : ℚ) * (source es hne).failure A + (T.gadget f hf).stabilityError / 2 ≤
        (k : ℚ) * FinalParameters.gamma (GapSemantics.errorValue error) k +
          (GapSemantics.errorValue error / 2) / 2 := by linarith
    _ = GapSemantics.errorValue error / 2 := FinalParameters.completeness_budget hk
    _ ≤ GapSemantics.errorValue error := by
      have hpos := GapSemantics.errorValue_pos error
      linarith

end MaxCutGames.Reduction.UniformReduction

namespace MaxCutGames.Reduction.OutputTranslations

open Integration.BinaryLinear
open ActualSource
open Foundations.Target

/-- A forward table translates every binary vector by the same offset sum. -/
theorem translationTable_vector {s : Nat} (a b x : Vector s) :
    (Encoding.translationTable a b).images[Encoding.alphabetEquiv s x] =
      Encoding.alphabetEquiv s (x + (a + b)) := by
  simpa only [add_assoc] using Encoding.translationTable_images a b x

/-- The same law on every numbered alphabet label, in fixed vector coordinates. -/
theorem translationTable_coordinates {s : Nat} (a b : Vector s) (label : Fin (2^s)) :
    (Encoding.alphabetEquiv s).symm ((Encoding.translationTable a b).images[label]) =
      (Encoding.alphabetEquiv s).symm label + (a + b) := by
  have h := translationTable_vector a b ((Encoding.alphabetEquiv s).symm label)
  simpa only [Encoding.alphabetEquiv_apply_symm_apply,
    Encoding.alphabetEquiv_symm_apply_apply] using
    congrArg (Encoding.alphabetEquiv s).symm h

/-- Every actual explicit edge has a concrete translation vector. -/
theorem explicitEdge_vector (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : ActualGame.Outcome S k g) :
    ∃ shift : Vector s, ∀ x : Vector s,
      (ActualGame.explicitEdge S k g ω).permutation.images[Encoding.alphabetEquiv s x] =
        Encoding.alphabetEquiv s (x + shift) := by
  refine ⟨ActualGame.offset S k s d (ActualGame.leftQuery S k g ω) +
    ActualGame.offset S k s d (ActualGame.rightQuery S k g ω), ?_⟩
  intro x
  exact translationTable_vector _ _ x

theorem explicitEdge_coordinates (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : ActualGame.Outcome S k g) :
    ∃ shift : Vector s, ∀ label : Fin (2^s),
      (Encoding.alphabetEquiv s).symm
          ((ActualGame.explicitEdge S k g ω).permutation.images[label]) =
        (Encoding.alphabetEquiv s).symm label + shift := by
  refine ⟨ActualGame.offset S k s d (ActualGame.leftQuery S k g ω) +
    ActualGame.offset S k s d (ActualGame.rightQuery S k g ω), ?_⟩
  intro label
  exact translationTable_coordinates _ _ label

/-- All emitted occurrences, including parallel edges and repeated noise values,
use translations in the same alphabet coordinates. -/
theorem outputInstanceWithEnumeration_vector (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    ∀ constraint ∈ (ActualGame.outputInstanceWithEnumeration S k g en).constraints,
      ∃ shift : Vector s, ∀ x : Vector s,
        constraint.permutation.images[Encoding.alphabetEquiv s x] =
          Encoding.alphabetEquiv s (x + shift) := by
  intro constraint hconstraint
  obtain ⟨ω, _, rfl⟩ := List.mem_map.mp hconstraint
  exact explicitEdge_vector S k g ω

theorem outputInstanceWithEnumeration_coordinates (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    ∀ constraint ∈ (ActualGame.outputInstanceWithEnumeration S k g en).constraints,
      ∃ shift : Vector s, ∀ label : Fin (2^s),
        (Encoding.alphabetEquiv s).symm (constraint.permutation.images[label]) =
          (Encoding.alphabetEquiv s).symm label + shift := by
  intro constraint hconstraint
  obtain ⟨ω, _, rfl⟩ := List.mem_map.mp hconstraint
  exact explicitEdge_coordinates S k g ω

/-- Erasing the correcting-map witness leaves the translation promise intact. -/
theorem tableOutput_vector (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) :
    ∀ constraint ∈ (Integration.TableReduction.output S k T).constraints,
      ∃ shift : Vector s, ∀ x : Vector s,
        constraint.permutation.images[Encoding.alphabetEquiv s x] =
          Encoding.alphabetEquiv s (x + shift) :=
  outputInstanceWithEnumeration_vector S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

theorem tableOutput_coordinates (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) :
    ∀ constraint ∈ (Integration.TableReduction.output S k T).constraints,
      ∃ shift : Vector s, ∀ label : Fin (2^s),
        (Encoding.alphabetEquiv s).symm (constraint.permutation.images[label]) =
          (Encoding.alphabetEquiv s).symm label + shift :=
  outputInstanceWithEnumeration_coordinates S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

theorem uniformOutput_vector {n s d : Nat}
    (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) (k : Nat)
    (T : Integration.NoiseTables.Table s d) :
    ∀ constraint ∈ (UniformReduction.output es hne k T).constraints,
      ∃ shift : Vector s, ∀ x : Vector s,
        constraint.permutation.images[Encoding.alphabetEquiv s x] =
          Encoding.alphabetEquiv s (x + shift) :=
  tableOutput_vector (UniformReduction.source es hne) k T

theorem uniformOutput_coordinates {n s d : Nat}
    (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) (k : Nat)
    (T : Integration.NoiseTables.Table s d) :
    ∀ constraint ∈ (UniformReduction.output es hne k T).constraints,
      ∃ shift : Vector s, ∀ label : Fin (2^s),
        (Encoding.alphabetEquiv s).symm (constraint.permutation.images[label]) =
          (Encoding.alphabetEquiv s).symm label + shift :=
  tableOutput_coordinates (UniformReduction.source es hne) k T

end MaxCutGames.Reduction.OutputTranslations

end OAI
