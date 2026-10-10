import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorNumericWork

namespace OAI

/-! # Expected scans of the actual checker at the manuscript's exponent -/

noncomputable section

namespace LowSpaceSubsetSum.SeparatorExpectation

open RepresentationMoments
open scoped BigOperators

/-- Numerical consequences of the prescribed rounded sample sizes. -/
structure RoundedParameters (g : ℕ) where
  e : Fin 4 → ℕ
  c : Fin 4 → ℕ
  density : ℝ
  large : 64 ≤ g
  even : 2 ∣ g
  count_le : ∀ i, c i ≤ e i
  size_le : ∀ i, e i ≤ g
  feasible : ∀ i, e i - c i ≤ g / 2
  density_mem : density ∈ Set.Icc (1 / 6) (1 / 3)
  count_error : ∀ i, |(c i : ℝ) - (g : ℝ) * density| ≤ 1
  size_error : ∀ i, |(e i : ℝ) - (g : ℝ) * (density + separatorY density)| ≤ 2

namespace RoundedParameters

variable {g : ℕ} (S : RoundedParameters g)

def counts : Fin 4 → ℕ :=
  fun i => ⌈10 / ((Nat.choose (g / 2) (S.e i - S.c i) : ℝ) / Nat.choose g (S.e i))⌉₊

def leftCharge (x : SeparatorCheck.Record g) : ℝ := ∏ i : Fin 4,
  (1 + (S.counts i : ℝ) * ((Nat.choose (g - (SeparatorCheck.localMask i x.mask).card)
    (S.e i - (SeparatorCheck.localMask i x.mask).card) : ℝ) / Nat.choose g (S.e i)))

def rightCharge (y : SeparatorCheck.Record g) : ℝ := ∏ i : Fin 4,
  (1 + (S.counts i : ℝ) * ((Nat.choose (g - (SeparatorCheck.localMask i y.mask).card)
    (S.e i) : ℝ) / Nat.choose g (S.e i)))

def chargeBound (_S : RoundedParameters g) (u : ℕ) : ℝ := (u : ℝ) ^ 20 *
  (2 : ℝ) ^ (((4 * g : ℕ) : ℝ) * (1 - binaryEntropy (1 / 4)))

theorem count_half (i : Fin 4) : S.c i ≤ g / 2 := by
  have hcu := (abs_le.mp (S.count_error i)).2
  have hgc := mul_le_mul_of_nonneg_left S.density_mem.2 (Nat.cast_nonneg g)
  have hgR : (64 : ℝ) ≤ g := by exact_mod_cast S.large
  have hhalf : ((g / 2 : ℕ) : ℝ) = (g : ℝ) / 2 := Nat.cast_div S.even (by norm_num)
  have h : (S.c i : ℝ) ≤ (g / 2 : ℕ) := by rw [hhalf]; nlinarith
  exact_mod_cast h

theorem counts_depth (i : Fin 4) : Nat.clog 2 (S.counts i) ≤ g + 4 :=
  rounded_family_depth g (S.e i) (S.c i) (S.size_le i) (S.feasible i)
    (separator_denominator_le g (S.e i) (S.c i) (S.count_half i) (S.count_le i))

theorem left_charge_nonneg (x : SeparatorCheck.Record g) : 0 ≤ S.leftCharge x := by
  unfold leftCharge
  positivity

theorem right_charge_nonneg (x : SeparatorCheck.Record g) : 0 ≤ S.rightCharge x := by
  unfold rightCharge
  positivity

theorem left_charge_le (u : ℕ) (hu : 256 ≤ u) (hgu : g + 1 ≤ u)
    (x : SeparatorCheck.Record g) (hx : ∀ i, (SeparatorCheck.localMask i x.mask).card = S.c i) :
    S.leftCharge x ≤ S.chargeBound u := by
  apply incidence_product_le g u hu hgu
  · intro i
    positivity
  · intro i
    rw [hx i]
    exact rounded_containment_incidence g (S.c i) (S.e i) S.large S.even (S.count_le i)
      (S.size_le i) (S.feasible i) S.density_mem (S.count_error i) (S.size_error i)

theorem right_charge_le (u : ℕ) (hu : 256 ≤ u) (hgu : g + 1 ≤ u)
    (x : SeparatorCheck.Record g)
    (hx : ∀ i, (SeparatorCheck.localMask i x.mask).card = g / 2 - S.c i) :
    S.rightCharge x ≤ S.chargeBound u := by
  apply incidence_product_le g u hu hgu
  · intro i
    positivity
  · intro i
    rw [hx i]
    exact rounded_avoidance_incidence g (S.c i) (S.e i) S.large S.even (S.count_half i)
      (S.count_le i) (S.size_le i) (S.feasible i) S.density_mem (S.count_error i) (S.size_error i)

private theorem map_sum_le {α : Type*} (xs : List α) (f : α → ℝ) (Q : ℝ)
    (h : ∀ x ∈ xs, f x ≤ Q) : (xs.map f).sum ≤ (xs.length : ℝ) * Q := by
  have hs := (xs.map f).sum_le_length_nsmul Q (by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact h x hx)
  simpa only [List.length_map, nsmul_eq_mul] using hs

theorem total_charge_le (u : ℕ) (hu : 256 ≤ u) (hgu : g + 1 ≤ u)
    (xs ys : List (SeparatorCheck.Record g))
    (hleft : ∀ x ∈ xs, ∀ i, (SeparatorCheck.localMask i x.mask).card = S.c i)
    (hright : ∀ x ∈ ys, ∀ i, (SeparatorCheck.localMask i x.mask).card = g / 2 - S.c i) :
    (xs.map S.leftCharge).sum + (ys.map S.rightCharge).sum ≤
      ((xs.length + ys.length : ℕ) : ℝ) * S.chargeBound u := by
  have hl := map_sum_le xs S.leftCharge (S.chargeBound u)
    (fun x hx => S.left_charge_le u hu hgu x (hleft x hx))
  have hr := map_sum_le ys S.rightCharge (S.chargeBound u)
    (fun x hx => S.right_charge_le u hu hgu x (hright x hx))
  push_cast
  nlinarith

theorem mean_scans_polynomial (n u : ℕ) (hu : 256 ≤ u) (hnu : n ≤ u) (hgu : g + 1 ≤ u)
    (target : ℤ) (xs ys : List (SeparatorCheck.Record g))
    (hleft : ∀ x ∈ xs, ∀ i, (SeparatorCheck.localMask i x.mask).card = S.c i)
    (hright : ∀ x ∈ ys, ∀ i, (SeparatorCheck.localMask i x.mask).card = g / 2 - S.c i) :
    mean (fun draws : IndependentFamilies g S.e S.counts =>
      ((SeparatorCheck.run n (familyArrays draws) target xs ys).scans : ℝ)) ≤
        ((xs.length + ys.length : ℕ) : ℝ) * (u : ℝ) ^ 22 *
          (2 : ℝ) ^ (((4 * g : ℕ) : ℝ) * (1 - binaryEntropy (1 / 4))) := by
  have hscan := mean_scans_le n S.e S.counts S.size_le target xs ys (by
    intro x hx i
    rw [hleft x hx i]
    exact S.count_le i)
  change _ ≤ ((6 * n + 8 + 2 * ∑ i : Fin 4, Nat.clog 2 (S.counts i) : ℕ) : ℝ) *
    ((xs.map S.leftCharge).sum + (ys.map S.rightCharge).sum) at hscan
  have hcoef := separator_coefficient_le n g u hu hnu hgu S.counts S.counts_depth
  have hsum := S.total_charge_le u hu hgu xs ys hleft hright
  have hsum0 : 0 ≤ (xs.map S.leftCharge).sum + (ys.map S.rightCharge).sum := by
    apply add_nonneg
    · apply List.sum_nonneg
      intro a ha
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
      exact S.left_charge_nonneg x
    · apply List.sum_nonneg
      intro a ha
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
      exact S.right_charge_nonneg x
  apply hscan.trans
  calc
    _ ≤ (u : ℝ) ^ 2 * (((xs.length + ys.length : ℕ) : ℝ) * S.chargeBound u) :=
      mul_le_mul hcoef hsum hsum0 (by positivity)
    _ = _ := by unfold chargeBound; ring

end RoundedParameters
end LowSpaceSubsetSum.SeparatorExpectation

end

end OAI
