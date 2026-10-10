import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import OAI.Computability.UniqueGames.Decoding.UniformConditioning
import OAI.Computability.UniqueGames.Foundations.Conditioning
import OAI.Computability.UniqueGames.Foundations.MixtureLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Decoder.VisibleTransfer

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Ω D : Type*} [Fintype Ω] [Fintype D]

/-- The part of an event in one actual visible-data fiber. -/
def fiberEvent (observe : Ω → D) (d : D) (event : Ω → Bool) : Ω → Bool := by
  classical
  exact fun x => decide (observe x = d) && event x

def fiberMass (μ : FiniteDistribution Ω) (observe : Ω → D)
    (d : D) (event : Ω → Bool) : ℝ :=
  μ.probability (fiberEvent observe d event)

omit [Fintype D] in
theorem fiberMass_nonnegative (μ : FiniteDistribution Ω) (observe : Ω → D)
    (d : D) (event : Ω → Bool) : 0 ≤ fiberMass μ observe d event :=
  μ.probability_nonnegative _

omit [Fintype D] in
theorem fiberMass_mono (μ : FiniteDistribution Ω) (observe : Ω → D)
    (d : D) {event event' : Ω → Bool}
    (h : ∀ x, event x = true → event' x = true) :
    fiberMass μ observe d event ≤ fiberMass μ observe d event' := by
  apply μ.probability_mono
  intro x hx
  simp only [fiberEvent, Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
  exact ⟨hx.1, h x hx.2⟩

theorem sum_fiberMass (μ : FiniteDistribution Ω) (observe : Ω → D)
    (event : Ω → Bool) :
    ∑ d, fiberMass μ observe d event = μ.probability event := by
  classical
  unfold fiberMass FiniteDistribution.probability fiberEvent
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases event x <;> simp

theorem observation_weight (μ : FiniteDistribution Ω) (observe : Ω → D) (d : D) :
    (μ.pushforward observe).weight d = fiberMass μ observe d (fun _ => true) := by
  classical
  simp [FiniteDistribution.pushforward, fiberMass, FiniteDistribution.probability,
    fiberEvent]

/-- Positive projected column-slice mass and sufficient conditional target
agreement. Both quantities are computed after fixing actual visible data. -/
def visibleWitness (μ : FiniteDistribution Ω) (observe : Ω → D)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (d : D) : Bool := by
  classical
  exact decide (0 < fiberMass μ observe d slice ∧
    threshold * fiberMass μ observe d slice ≤
      fiberMass μ observe d (fun x => slice x && targetHit x))

/-- The positive part of the witness margin is paid for by the probability of
the actual observed data, rather than by the larger hidden sample space. -/
theorem witness_margin_le_visible_probability
    (μ : FiniteDistribution Ω) (observe : Ω → D)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    μ.probability (fun x => slice x && targetHit x) - threshold * μ.probability slice ≤
      (μ.pushforward observe).probability (visibleWitness μ observe slice targetHit threshold) := by
  classical
  have pointwise (d : D) :
      fiberMass μ observe d (fun x => slice x && targetHit x) -
          threshold * fiberMass μ observe d slice ≤
        if visibleWitness μ observe slice targetHit threshold d then
          (μ.pushforward observe).weight d else 0 := by
    have hs := fiberMass_nonnegative μ observe d slice
    have hm := fiberMass_nonnegative μ observe d (fun x => slice x && targetHit x)
    have hms : fiberMass μ observe d (fun x => slice x && targetHit x) ≤
        fiberMass μ observe d slice := by
      apply fiberMass_mono
      intro x hx
      simp only [Bool.and_eq_true] at hx
      exact hx.1
    have hmo : fiberMass μ observe d (fun x => slice x && targetHit x) ≤
        (μ.pushforward observe).weight d := by
      rw [observation_weight]
      exact fiberMass_mono μ observe d (fun _ _ => rfl)
    by_cases hgood : visibleWitness μ observe slice targetHit threshold d = true
    · simp only [hgood, ↓reduceIte]
      exact (sub_le_self _ (mul_nonneg hthreshold hs)).trans hmo
    · simp only [hgood, Bool.false_eq_true, ↓reduceIte]
      by_cases hpos : 0 < fiberMass μ observe d slice
      · have hnot : ¬ threshold * fiberMass μ observe d slice ≤
            fiberMass μ observe d (fun x => slice x && targetHit x) := by
          intro hle
          exact hgood (by simp [visibleWitness, hpos, hle])
        linarith
      · have hzero : fiberMass μ observe d slice = 0 := le_antisymm (le_of_not_gt hpos) hs
        rw [hzero, mul_zero, sub_zero]
        exact hms.trans_eq hzero
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun d _ => pointwise d
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_fiberMass,
    FiniteDistribution.probability] using hsum

omit [Fintype D] in
/-- On every selected datum the conditional distribution is defined on an
actual nonempty positive-mass slice and has the promised target agreement. -/
theorem visibleWitness_conditional
    (μ : FiniteDistribution Ω) (observe : Ω → D)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (d : D)
    (h : visibleWitness μ observe slice targetHit threshold d = true) :
    ∃ hpositive : 0 < μ.probability (fiberEvent observe d slice),
      threshold ≤ (μ.condition (fiberEvent observe d slice) hpositive).probability targetHit := by
  classical
  have hh : 0 < fiberMass μ observe d slice ∧
      threshold * fiberMass μ observe d slice ≤
        fiberMass μ observe d (fun x => slice x && targetHit x) := by
    simpa only [visibleWitness, decide_eq_true_eq] using h
  unfold fiberMass at hh
  refine ⟨hh.1, ?_⟩
  rw [FiniteDistribution.probability_condition]
  have hsame : (fun x => fiberEvent observe d slice x && targetHit x) =
      fiberEvent observe d (fun x => slice x && targetHit x) := by
    funext x
    simp [fiberEvent, Bool.and_assoc]
  rw [hsame]
  exact (le_div_iff₀ hh.1).mpr hh.2

omit [Fintype D] in
/-- Goodness is inherited from any event whose membership requires good
visible advice. Positivity supplies an actual supporting hidden sample. -/
theorem visibleWitness_good
    (μ : FiniteDistribution Ω) (observe : Ω → D)
    (slice targetHit : Ω → Bool) (threshold : ℝ)
    (good : D → Prop) (hslice : ∀ x, slice x = true → good (observe x))
    (d : D) (h : visibleWitness μ observe slice targetHit threshold d = true) :
    good d := by
  classical
  have hpos : 0 < fiberMass μ observe d slice := by
    have hh := of_decide_eq_true h
    exact hh.1
  by_contra hbad
  have hempty : fiberEvent observe d slice = fun _ => false := by
    funext x
    apply Bool.eq_false_iff.mpr
    intro hx
    have hh : observe x = d ∧ slice x = true := by
      simpa only [fiberEvent, Bool.and_eq_true, decide_eq_true_eq] using hx
    exact hbad (hh.1 ▸ hslice x hh.2)
  unfold fiberMass at hpos
  rw [hempty, FiniteDistribution.probability_false] at hpos
  exact (lt_irrefl 0) hpos

/-- A pair of full-table event probabilities transfers with error
`(1 + threshold) * TV`. This estimate precedes all conditioning. -/
theorem margin_transfer (μ ν : FiniteDistribution Ω)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    μ.probability (fun x => slice x && targetHit x) - threshold * μ.probability slice -
        (1 + threshold) * μ.totalVariation ν ≤
      ν.probability (fun x => slice x && targetHit x) - threshold * ν.probability slice := by
  have hm := μ.probability_sub_le_totalVariation ν (fun x => slice x && targetHit x)
  have hs := ν.probability_sub_le_totalVariation μ slice
  rw [FiniteDistribution.totalVariation_comm] at hs
  have hscaled := mul_le_mul_of_nonneg_left hs hthreshold
  nlinarith

/-- The whole-table comparison and the exact finite disintegration combine
without any assumption on conditional projection laws. -/
theorem wholeTable_transfer_to_visibleWitness
    {Γ : Type*} [Fintype Γ]
    (unrestricted : FiniteDistribution Ω) (actual : FiniteDistribution Γ)
    (pad : Γ → Ω) (observe : Γ → D) (slice targetHit : Ω → Bool)
    (threshold γ : ℝ) (hthreshold : 0 ≤ threshold)
    (hmargin : γ ≤
      unrestricted.probability (fun x => slice x && targetHit x) -
        threshold * unrestricted.probability slice -
        (1 + threshold) * unrestricted.totalVariation (actual.pushforward pad)) :
    γ ≤ (actual.pushforward observe).probability
      (visibleWitness actual observe (fun x => slice (pad x))
        (fun x => targetHit (pad x)) threshold) := by
  have transferred := margin_transfer unrestricted (actual.pushforward pad)
    slice targetHit threshold hthreshold
  simp only [FiniteDistribution.probability_pushforward] at transferred
  exact (hmargin.trans transferred).trans
    (witness_margin_le_visible_probability actual observe
      (fun x => slice (pad x)) (fun x => targetHit (pad x)) threshold hthreshold)

theorem projected_witness_mass
    {Γ : Type*} [Fintype Γ]
    (unrestricted : FiniteDistribution Ω) (actual : FiniteDistribution Γ)
    (pad : Γ → Ω) (observe : Γ → D) (slice targetHit : Ω → Bool)
    (α g₀ c : ℝ) (hα : 0 ≤ α)
    (hslice : g₀ * c ≤ unrestricted.probability slice)
    (hagreement : (α / 2) * unrestricted.probability slice ≤
      unrestricted.probability (fun x => slice x && targetHit x))
    (herror : (1 + α / 4) * unrestricted.totalVariation (actual.pushforward pad) ≤
      α * g₀ * c / 8) :
    α * g₀ * c / 8 ≤ (actual.pushforward observe).probability
      (visibleWitness actual observe (fun x => slice (pad x))
        (fun x => targetHit (pad x)) (α / 4)) := by
  apply wholeTable_transfer_to_visibleWitness unrestricted actual pad observe slice targetHit
    (α / 4) (α * g₀ * c / 8) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hslice (show 0 ≤ α / 4 by positivity)
  nlinarith

end
end UniqueGamesTheorem.Decoder.VisibleTransfer

end

section

namespace UniqueGamesTheorem.Decoder.UniformFibers

open Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {Ω D Y : Type*}

def selectedFiberEquiv (observe : Ω → D) (d : D) (slice : Ω → Bool)
    (e : Y ≃ {x : Ω // observe x = d}) :
    {x : Ω // VisibleTransfer.fiberEvent observe d slice x = true} ≃
      {y : Y // slice (e y).val = true} where
  toFun x := by
    have hx : observe x.val = d ∧ slice x.val = true := by
      simpa only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq] using x.property
    refine ⟨e.symm ⟨x.val, hx.1⟩, ?_⟩
    simpa only [Equiv.apply_symm_apply] using hx.2
  invFun y := ⟨(e y.val).val, by
    simp only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(e y.val).property, y.property⟩⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    simp only [Equiv.apply_symm_apply]
  right_inv y := by
    apply Subtype.ext
    exact e.symm_apply_apply y.val

theorem selectedFiberEquiv_point (observe : Ω → D) (d : D) (slice : Ω → Bool)
    (e : Y ≃ {x : Ω // observe x = d})
    (x : {x : Ω // VisibleTransfer.fiberEvent observe d slice x = true}) :
    (e (selectedFiberEquiv observe d slice e x).val).val = x.val := by
  exact congrArg Subtype.val (e.apply_symm_apply _)

/-- Conditioning after fixing the complete datum and the selected column
event leaves precisely the uniform restricted private fiber. -/
theorem conditional_probability [Fintype Ω] [Fintype Y]
    (μ : FiniteDistribution Ω) (observe : Ω → D) (d : D)
    (slice event : Ω → Bool)
    (positive : 0 < μ.probability (VisibleTransfer.fiberEvent observe d slice))
    (c : ℝ) (hconstant : ∀ x, observe x = d → μ.weight x = c)
    (e : Y ≃ {x : Ω // observe x = d}) :
    (μ.condition (VisibleTransfer.fiberEvent observe d slice) positive).probability event =
      𝔼 y : {y : Y // slice (e y).val = true},
        if event (e y.val).val then (1 : ℝ) else 0 := by
  apply UniformConditioning.condition_probability_equiv μ
    (VisibleTransfer.fiberEvent observe d slice) event positive c
    (fun x hx => hconstant x (by
      have h : observe x = d ∧ slice x = true := by
        simpa only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq] using hx
      exact h.1))
    (selectedFiberEquiv observe d slice e)
    (fun y => event (e y.val).val)
  intro x
  rw [selectedFiberEquiv_point]

end
end UniqueGamesTheorem.Decoder.UniformFibers

end

end OAI
