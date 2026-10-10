import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Reduction.ActualCanonicalLemmas
import OAI.Computability.UniqueGames.Reduction.WeightRounding

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.WeightedSource

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

section E3Lin

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

end E3Lin

end UniqueGamesTheorem.Reduction.WeightedSource

end

end OAI
