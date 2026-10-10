import OAI.Computability.PerfectCompleteness.Foundations.FiniteProduct
import OAI.Computability.PerfectCompleteness.Reduction.OccurrenceGame
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.Games.CompletedSamplingLemmas
import OAI.Computability.UniqueGames.Soundness.PartnerLinearLemmas

namespace OAI


namespace PerfectCompleteness.RepetitionRate

open scoped BigOperators
open UniqueGamesTheorem.Foundations Games

def halfRate (L : Nat) : ℚ := 1 - 1 / (48000 * (L : ℚ))

theorem halfRate_bounds {L : Nat} (hL : 0 < L) :
    0 < halfRate L ∧ halfRate L < 1 := by
  have hLq : (1 : ℚ) ≤ L := by exact_mod_cast hL
  have hden : (0 : ℚ) < 48000 * L := by positivity
  have hpos : (0 : ℚ) < 1 / (48000 * L) := div_pos zero_lt_one hden
  have hlt : (1 : ℚ) / (48000 * L) < 1 :=
    (div_lt_one hden).2 (by linarith)
  constructor <;> unfold halfRate <;> linarith

theorem halfRate_cast (L : Nat) :
    (halfRate L : ℝ) = 1 - 1 / (48000 * (L : ℝ)) := by
  simp only [halfRate, Rat.cast_sub, Rat.cast_one, Rat.cast_div,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]

theorem halfRate_power_comparison {L : Nat} (hL : 0 < L) :
    (1 - 1 / 48000 : ℝ) ≤ (halfRate L : ℝ) ^ L := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hden : (0 : ℝ) < 48000 * L := by positivity
  have hfrac : (1 : ℝ) / (48000 * L) ≤ 1 :=
    (div_le_one hden).2 (by linarith)
  have h := one_add_mul_le_pow
    (a := -((1 : ℝ) / (48000 * L))) (by linarith :
      (-2 : ℝ) ≤ -((1 : ℝ) / (48000 * L))) L
  rw [halfRate_cast]
  calc
    (1 - 1 / 48000 : ℝ) =
      1 + (L : ℝ) * (-((1 : ℝ) / (48000 * L))) := by
      field_simp [ne_of_gt hLpos]
      ring
    _ ≤ (1 + -((1 : ℝ) / (48000 * L))) ^ L := h
    _ = (1 - 1 / (48000 * (L : ℝ))) ^ L := by rw [sub_eq_add_neg]

theorem halfRate_rpow_comparison {L : Nat} (hL : 0 < L) (n : Nat) :
    (1 - 1 / 48000 : ℝ) ^ ((n : ℝ) / L) ≤ (halfRate L : ℝ) ^ n := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hr : (0 : ℝ) ≤ halfRate L := by
    exact_mod_cast (halfRate_bounds hL).1.le
  calc
    _ ≤ ((halfRate L : ℝ) ^ L) ^ ((n : ℝ) / L) :=
      Real.rpow_le_rpow (by norm_num) (halfRate_power_comparison hL) (by positivity)
    _ = (halfRate L : ℝ) ^ ((L : ℝ) * ((n : ℝ) / L)) :=
      (Real.rpow_natCast_mul hr L ((n : ℝ) / L)).symm
    _ = (halfRate L : ℝ) ^ (n : ℝ) := by
      congr 1
      field_simp [ne_of_gt hLpos]
    _ = (halfRate L : ℝ) ^ n := Real.rpow_natCast _ _

theorem game_repetition_halfRate {Q₁ Q₂ A₁ A₂ : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
    [Nonempty A₁] [Nonempty A₂] [DecidableEq Q₁] [DecidableEq Q₂]
    (G : Game Q₁ Q₂ A₁ A₂) {L : Nat} (hL : 0 < L)
    (halphabet : Repetition.logTwo
      ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ L)
    (hvalue : G.value ≤ 1 / 2) (n : Nat) :
    (G.repetition n).value ≤ (halfRate L : ℝ) ^ n := by
  have hell : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h := Repetition.holenstein_repetition_value G n hvalue
    (by norm_num : (1 / 2 : ℝ) < 1) hell halphabet
  have hbase : (1 - (1 - (1 / 2 : ℝ)) ^ 3 / 6000) = 1 - 1 / 48000 := by
    norm_num
  rw [hbase] at h
  exact h.trans (halfRate_rpow_comparison hL n)

theorem occurrence_repetition_halfRate {E Q₁ Q₂ A₁ A₂ : Type*}
    [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
    [Nonempty A₁] [Nonempty A₂] [DecidableEq Q₁] [DecidableEq Q₂]
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (p : G.EndpointPresentation)
    {L : Nat} (hL : 0 < L)
    (halphabet : Repetition.logTwo
      ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ L)
    (hvalue : G.value ≤ 1 / 2) (n : Nat) :
    (G.repetition n).value ≤ (halfRate L : ℝ) ^ n := by
  have hv : (G.toGame p).value ≤ 1 / 2 := by
    simpa only [G.toGame_value p] using hvalue
  have h := game_repetition_halfRate (G.toGame p) hL halphabet hv n
  simpa only [G.toGame_repetition_value p n] using h

noncomputable section

def bernoulli (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) : FiniteDistribution Bool where
  weight b := if b = true then p else 1 - p
  nonnegative b := by
    cases b
    · simpa using sub_nonneg.mpr hp'
    · simpa using hp
  normalized := by simp

def cleanCount {n : Nat} (mask : Fin n → Bool) : Nat :=
  (Finset.univ.filter fun i => mask i = true).card

theorem pow_cleanCount_eq_prod {n : Nat} (a : ℝ) (mask : Fin n → Bool) :
    a ^ cleanCount mask = ∏ i, if mask i = true then a else 1 := by
  rw [← Finset.prod_filter]
  simp [cleanCount]

theorem cleanMask_moment (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (a : ℝ) (n : Nat) :
    ((bernoulli p hp hp').iid n).expectation (fun mask => a ^ cleanCount mask) =
      (1 - p * (1 - a)) ^ n := by
  unfold FiniteDistribution.expectation FiniteDistribution.iid
  simp_rw [pow_cleanCount_eq_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.sum_pow
    (fun b : Bool => (bernoulli p hp hp').weight b * (if b = true then a else 1)) n]
  congr 1
  simp [bernoulli]
  ring

end

theorem cube_decay_bound {c : ℚ} (hc : 0 ≤ c) (hc' : c ≤ 1)
    {m : Nat} (hm : 0 < m) :
    (1 - c / (m : ℚ) ^ 2) ^ (m ^ 3) ≤ 1 / (1 + c * m) := by
  have hmone : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℚ) < m := by exact_mod_cast hm
  have hmsq : (1 : ℚ) ≤ (m : ℚ) ^ 2 := by nlinarith
  have hsqpos : (0 : ℚ) < (m : ℚ) ^ 2 := pow_pos hmpos _
  have hfrac0 : (0 : ℚ) ≤ c / (m : ℚ) ^ 2 := div_nonneg hc hsqpos.le
  have hfrac1 : c / (m : ℚ) ^ 2 ≤ 1 := (div_le_one hsqpos).2 (hc'.trans hmsq)
  have h := UniqueGamesTheorem.Soundness.RepetitionUpper.power_mul_growth_le_one
    (1 - c / (m : ℚ) ^ 2) (by linarith) (by linarith) (m ^ 3)
  have hfactor : 1 + ((m ^ 3 : Nat) : ℚ) * (1 - (1 - c / (m : ℚ) ^ 2)) =
      1 + c * m := by
    push_cast
    field_simp [ne_of_gt hmpos]
    ring
  rw [hfactor] at h
  have hden : (0 : ℚ) < 1 + c * m := by positivity
  exact (le_div_iff₀ hden).2 h

theorem exists_cube_decay_lt {c threshold : ℚ}
    (hc : 0 < c) (hc' : c ≤ 1) (hthreshold : 0 < threshold) :
    ∃ m : Nat, 0 < m ∧
      (1 - c / (m : ℚ) ^ 2) ^ (m ^ 3) < threshold := by
  obtain ⟨m, hm, hlarge⟩ :=
    UniqueGamesTheorem.Soundness.RepetitionUpper.exists_pos_nat_gt (1 / (c * threshold))
  refine ⟨m, hm, (cube_decay_bound hc.le hc' hm).trans_lt ?_⟩
  have hlarge' : (1 : ℚ) < (m : ℚ) * (c * threshold) :=
    (div_lt_iff₀ (mul_pos hc hthreshold)).1 hlarge
  have hden : (0 : ℚ) < 1 + c * m := by positivity
  apply (div_lt_iff₀ hden).2
  nlinarith

theorem exists_clean_branching {L : Nat} (hL : 0 < L) {p0 threshold : ℚ}
    (hp0 : 0 < p0) (hp0' : p0 ≤ 1) (hthreshold : 0 < threshold) :
    ∃ m : Nat, 0 < m ∧
      (1 - ((1 - halfRate L) * p0) / (m : ℚ) ^ 2) ^ (m ^ 3) < threshold := by
  have hr := halfRate_bounds hL
  have hc : (0 : ℚ) < (1 - halfRate L) * p0 :=
    mul_pos (sub_pos.mpr hr.2) hp0
  have hc' : (1 - halfRate L) * p0 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hp0' (sub_nonneg.mpr hr.2.le)
    nlinarith
  exact exists_cube_decay_lt hc hc' hthreshold

end PerfectCompleteness.RepetitionRate



namespace PerfectCompleteness.IndexedRepetition

open UniqueGamesTheorem.Foundations.Games
open FiniteProduct

noncomputable section

variable {E Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def game (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (I : Type*)
    [Fintype I] [DecidableEq I] :
    OccurrenceGame (I → E) (I → Q₁) (I → Q₂) (I → A₁) (I → A₂) := by
  classical
  exact
    { occurrences := law (fun _ : I => G.occurrences)
      left := fun x i => G.left (x i)
      right := fun x i => G.right (x i)
      accepts := fun x a b => decide (∀ i, G.accepts (x i) (a i) (b i) = true) }

def reindexStrategy {I J : Type*} (e : J ≃ I)
    (s : Strategy (I → Q₁) (I → Q₂) (I → A₁) (I → A₂)) :
    Strategy (J → Q₁) (J → Q₂) (J → A₁) (J → A₂) :=
  (fun x j => s.1 (x ∘ e.symm) (e j),
   fun y j => s.2 (y ∘ e.symm) (e j))

theorem law_const_fin (μ : FiniteDistribution E) (n : Nat) :
    law (fun _ : Fin n => μ) = μ.iid n := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  rfl

theorem game_fin (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (n : Nat) :
    game G (Fin n) = G.repetition n := by
  unfold game OccurrenceGame.repetition
  simp only [law_const_fin]
  congr 1
  funext x a b
  by_cases h : ∀ i : Fin n, G.accepts (x i) (a i) (b i) = true <;>
    simp only [h, decide_false]

theorem reindex_law {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (μ : FiniteDistribution E) (e : J ≃ I) :
    (law (fun _ : I => μ)).pushforward (fun x => x ∘ e) =
      law (fun _ : J => μ) :=
  FiniteDistribution.table_const_reindex μ e

theorem reindex_success {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (e : J ≃ I)
    (s : Strategy (I → Q₁) (I → Q₂) (I → A₁) (I → A₂)) :
    (game G J).success (reindexStrategy e s) = (game G I).success s := by
  classical
  change (law (fun _ : J => G.occurrences)).probability _ =
    (law (fun _ : I => G.occurrences)).probability _
  rw [← reindex_law G.occurrences e, FiniteDistribution.probability_pushforward]
  apply congrArg (law (fun _ : I => G.occurrences)).probability
  funext x
  have hl : (fun j => G.left ((x ∘ e) j)) ∘ e.symm = fun i => G.left (x i) := by
    funext i
    simp only [Function.comp_apply, e.apply_symm_apply]
  have hr : (fun j => G.right ((x ∘ e) j)) ∘ e.symm = fun i => G.right (x i) := by
    funext i
    simp only [Function.comp_apply, e.apply_symm_apply]
  change decide (∀ j, G.accepts ((x ∘ e) j)
      (s.1 ((fun j => G.left ((x ∘ e) j)) ∘ e.symm) (e j))
      (s.2 ((fun j => G.right ((x ∘ e) j)) ∘ e.symm) (e j)) = true) =
    decide (∀ i, G.accepts (x i)
      (s.1 (fun i => G.left (x i)) i) (s.2 (fun i => G.right (x i)) i) = true)
  rw [hl, hr]
  congr 1
  apply propext
  constructor
  · intro h i
    simpa only [Function.comp_apply, e.apply_symm_apply] using h (e.symm i)
  · intro h j
    exact h (e j)

theorem success_le_repetition_value {I : Type*} [Fintype I] [DecidableEq I]
    [Nonempty A₁] [Nonempty A₂]
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (s : Strategy (I → Q₁) (I → Q₂) (I → A₁) (I → A₂)) :
    (game G I).success s ≤ (G.repetition (Fintype.card I)).value := by
  rw [← reindex_success G (Fintype.equivFin I).symm s, game_fin]
  exact (G.repetition (Fintype.card I)).success_le_value _

theorem value_eq_repetition {I : Type*} [Fintype I] [DecidableEq I]
    [Nonempty A₁] [Nonempty A₂] (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) :
    (game G I).value = (G.repetition (Fintype.card I)).value := by
  apply le_antisymm
  · exact ((game G I).value_le_iff _).2 (success_le_repetition_value G)
  · apply ((G.repetition (Fintype.card I)).value_le_iff _).2
    intro s
    have h := reindex_success G (Fintype.equivFin I) s
    rw [game_fin] at h
    rw [← h]
    exact (game G I).success_le_value (reindexStrategy (Fintype.equivFin I) s)

theorem halfRate {I : Type*} [Fintype I] [DecidableEq I]
    [Nonempty A₁] [Nonempty A₂] [DecidableEq Q₁] [DecidableEq Q₂]
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (p : G.EndpointPresentation)
    {L : Nat} (hL : 0 < L)
    (alphabet : UniqueGamesTheorem.Foundations.Repetition.logTwo
      ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ L)
    (gap : G.value ≤ 1 / 2) :
    (game G I).value ≤ (RepetitionRate.halfRate L : ℝ) ^ Fintype.card I := by
  rw [value_eq_repetition]
  exact RepetitionRate.occurrence_repetition_halfRate G p hL alphabet gap _

end
end PerfectCompleteness.IndexedRepetition

end OAI
