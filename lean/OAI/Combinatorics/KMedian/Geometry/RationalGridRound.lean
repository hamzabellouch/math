import Mathlib
import OAI.Combinatorics.KMedian.Preparation.AssignmentCopies
import OAI.Combinatorics.KMedian.Geometry.RationalCompletedCost
import OAI.Combinatorics.KMedian.Rounding.RationalRoundParameters
import OAI.Combinatorics.KMedian.Geometry.RationalNearestCopies
import OAI.Combinatorics.KMedian.Geometry.RationalHistorySelection

namespace OAI


                                         
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
open Preparation.RationalNearest
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [PseudoMetricSpace X] {j : ℕ}
local instance rationalGridRoundCopyOrder : LinearOrder (Copy (F := F) q.Δ) := copyOrder

def nearest (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ)) :
    Fin j → Finset (Copy (F := F) q.Δ) := fun c => takeNearest (fun a => d c a.1) q.Δ A

theorem nearest_nonempty (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ))
    (hA : q.Δ ≤ A.card) (c : Fin j) : (q.nearest d A c).Nonempty := by
  apply card_pos.mp
  change 0 < (takeNearest (fun a : Copy (F := F) q.Δ => d c a.1) q.Δ A).card
  rw [(takeNearest_spec (fun a : Copy (F := F) q.Δ => d c a.1) q.Δ A hA).2.1]
  exact q.Δpos

def radius (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ))
    (hA : q.Δ ≤ A.card) (c : Fin j) : ℚ :=
  ((q.nearest d A c).image (fun a => d c a.1)).max' ((q.nearest_nonempty d A hA c).image _)

theorem nearest_spec (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ))
    (hA : q.Δ ≤ A.card) (c : Fin j) :
    q.nearest d A c ⊆ A ∧ (q.nearest d A c).card=q.Δ :=
  ⟨(takeNearest_spec (fun a : Copy (F := F) q.Δ => d c a.1) q.Δ A hA).1,
    (takeNearest_spec (fun a : Copy (F := F) q.Δ => d c a.1) q.Δ A hA).2.1⟩

theorem radius_spec (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ))
    (hA : q.Δ ≤ A.card) (c : Fin j) :
    (∀ i∈q.nearest d A c, d c i.1 ≤ q.radius d A hA c) ∧
      ∃ i∈q.nearest d A c, q.radius d A hA c=d c i.1 := by
  constructor
  · intro i hi
    exact le_max' ((q.nearest d A c).image (fun a : Copy (F := F) q.Δ => d c a.1))
      (d c i.1) (mem_image.mpr ⟨i,hi,rfl⟩)
  · obtain ⟨i,hi,he⟩ := mem_image.mp (max'_mem
      ((q.nearest d A c).image (fun a : Copy (F := F) q.Δ => d c a.1))
        ((q.nearest_nonempty d A hA c).image _))
    exact ⟨i,hi,he.symm⟩

variable [Fintype F]

def roundCounts (d₀ : F → F → ℚ) (d : Fin j → F → ℚ) (n : F → ℕ) : Option (Finset F) :=
  if hn : ∀ a, n a ≤ q.Δ then
    let A := activeSlots n hn
    if hA : q.Δ ≤ A.card then
      q.selectCompleted d₀ d (q.radius d A hA) A (q.nearest d A) (q.nearest_nonempty d A hA)
    else none
  else none

theorem roundCounts_spec (hτ : τ<1) (hj : 0<j)
    (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (n : F → ℕ) (hn : ∀ a, n a ≤ q.Δ) (hm : 1 ≤ ∑ a, (q.g:ℝ)*(n a:ℝ))
    (r : Fin j → F → ℝ) (hr0 : ∀ c a, 0 ≤ r c a)
    (hr1 : ∀ c a, r c a ≤ (q.g:ℝ)*(n a:ℝ)) (hrsum : ∀ c, ∑ a, r c a=1) :
    ∃ O : Finset F, q.roundCounts d₀ d n=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ (∑ a, (q.g:ℝ)*(n a:ℝ))+(q.allowance:ℝ) ∧
      (score d O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(∑ c,∑ a, r c a*(d c a:ℝ)) := by
  let A := activeSlots n hn
  have hAm : 1 ≤ mass (q.g:ℝ) A := by rw [activeSlots_mass]; exact hm
  have hA : q.Δ ≤ A.card := by
    rw [← q.unit] at hAm
    exact_mod_cast (mul_le_mul_iff_right₀ q.gpos).mp hAm
  let B := q.nearest d A
  have hB : ∀ c, (B c).Nonempty := q.nearest_nonempty d A hA
  have hBc : ∀ c, (B c).card=q.Δ := fun c => (q.nearest_spec d A hA c).2
  have hBA : ∀ c, B c ⊆ A := fun c => (q.nearest_spec d A hA c).1
  have hBm : ∀ c, mass (q.g:ℝ) (B c)=1 := by intro c; rw [mass,hBc,q.unit]
  let R := q.radius d A hA
  have hdR : ∀ c i, i∈B c → d c i.1 ≤ R c := fun c => (q.radius_spec d A hA c).1
  have hatt : ∀ c, ∃ i∈B c, R c=d c i.1 := fun c => (q.radius_spec d A hA c).2
  have hR : ∀ c, 0 ≤ R c := by
    intro c
    obtain ⟨i,hi,he⟩ := hatt c
    rw [he]
    exact_mod_cast (hd c i.1 ▸ dist_nonneg)
  have hcost : ∀ c, PhysicalPotential.cost (q.g:ℝ)
      (fun i : Copy (F := F) q.Δ => dist (client c) (location i.1)) (B c) ≤
        ∑ a, r c a*(d c a:ℝ) := by
    intro c
    obtain ⟨S,hS,hmS,hcS⟩ := assignment_copies n hn (r c) (fun a => (d c a:ℝ))
      q.gpos q.unit (hr0 c) (hr1 c) (hrsum c)
    have hSc : S.card=q.Δ := by
      have he : (q.g:ℝ)*(S.card:ℝ)=(q.g:ℝ)*(q.Δ:ℝ) := hmS.trans q.unit.symm
      exact_mod_cast (mul_left_cancel₀ q.gpos.ne' he)
    have hl := (takeNearest_spec (fun a => d c a.1) q.Δ A hA).2.2 S hS hSc
    have hlR : (∑ a∈B c,(d c a.1:ℝ)) ≤ ∑ a∈S,(d c a.1:ℝ) := by exact_mod_cast hl
    calc
      _ = (q.g:ℝ)*∑ a∈B c,(d c a.1:ℝ) := by simp only [PhysicalPotential.cost,hd,mul_sum]
      _ ≤ (q.g:ℝ)*∑ a∈S,(d c a.1:ℝ) := mul_le_mul_of_nonneg_left hlR q.gpos.le
      _ ≤ _ := by simpa only [← mul_sum,PhysicalPotential.cost] using hcS
  obtain ⟨O,hO,hnO,hcard,hscore⟩ := q.selectCompleted_spec hτ hj d₀ d location client hd₀ hd
    A B R hB hAm hBA hR hBm hdR hatt
  refine ⟨O,?_,hnO,?_,hscore.trans ?_⟩
  · unfold roundCounts
    rw [dite_eq_left hn]
    change (if hA : q.Δ ≤ A.card then _ else none)=_
    rw [dite_eq_left hA]
    exact hO
  · simpa only [A,activeSlots_mass] using hcard
  · apply mul_le_mul_of_nonneg_left (sum_le_sum (fun c _ => hcost c))
    apply div_nonneg _ (sub_pos.mpr hτ).le
    have hτ0 : 0 ≤ τ := by
      have hh := q.failure
      have hnum : 0 ≤ (q.T:ℝ)*(96*(q.Δ:ℝ)^2*(q.β:ℝ)/
          ((2*(q.h:ℝ)*(q.g:ℝ))*(q.φ:ℝ)^2*(q.g:ℝ))) := by
        have hg := q.gpos; have hh := q.hpos; have hβ := q.βpos
        positivity
      exact hnum.trans hh
    positivity

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
