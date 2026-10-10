import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Profiles.Profile
import OAI.Combinatorics.BalancedRyser.Profiles.ProfilePoissonLemmas
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileVisibility

namespace OAI

open MeasureTheory
open scoped NNReal

namespace Balanced
open scoped _root_.Balanced
namespace ProfileVisibility

theorem recurrence_of_zero_deletionVisible (P : Profile)
    (νD : Measure Profile) [IsFiniteMeasure νD] {k : ℝ}
    (hmass : νD.real Set.univ = k)
    (hinc : ∀ i j : ℕ, (∫ x, x (i + 1, j) ∂νD) =
      (i + 1 : ℝ) * P (i + 1, j))
    (hzero : νD (deletionVisible P) = 0) :
    ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1, j) = k * P (i, j) := by
  have hinvis : ∀ᵐ x ∂νD, deletionInvisible P x := ae_iff.mpr hzero
  apply recurrence_of_invisible (fun i j => P (i, j)) (fun x i j => x (i, j)) hmass hinc
  intro i j
  filter_upwards [hinvis] with x hx
  simpa using hx (i + 1) j

theorem deletionVisible_pos_of_not_poisson (P : Profile)
    (νD : Measure Profile) [IsFiniteMeasure νD] (k : ℕ)
    (hmass : νD.real Set.univ = (k : ℝ))
    (hinc : ∀ i j : ℕ, (∫ x, x (i + 1, j) ∂νD) =
      (i + 1 : ℝ) * P (i + 1, j))
    (hnorm : HasSum (fun i => P (i, 0)) 1)
    (hnot : ∃ i, P (i, 0) ≠ deletionPoissonMass k i) :
    0 < νD.real (deletionVisible P) := by
  by_contra hpos
  have hreal : νD.real (deletionVisible P) = 0 :=
    le_antisymm (le_of_not_gt hpos) measureReal_nonneg
  have hzero : νD (deletionVisible P) = 0 := (measureReal_eq_zero_iff (by finiteness)).mp hreal
  have hrec := recurrence_of_zero_deletionVisible P νD hmass hinc hzero
  obtain ⟨i, hi⟩ := hnot
  apply hi
  exact profile_recurrence_eq_poissonMeasure (k : ℝ≥0) hnorm
    (fun n => hrec n 0) i

theorem coverVisible_mass_one (P : Profile)
    (νC : Measure Profile) [IsProbabilityMeasure νC] {μ : ℝ}
    (hμ : 0 < μ) (hcorner : P (0, 0) = 0)
    (hf : Integrable (fun x : Profile => x (0, 1)) νC)
    (hupper : ∀ᵐ x ∂νC, x (0, 1) ≤ μ)
    (hint : (∫ x, x (0, 1) ∂νC) = μ) :
    νC.real (coverVisible P) = 1 := by
  have hzero : ∀ x ∈ {x : Profile | coverInvisible P x}, x (0, 1) = 0 := by
    intro x hx
    simpa [hcorner] using hx 0 1
  have hfull := (saturated_coordinate_visible hμ hf hupper hint hzero).2
  change νC.real ({x : Profile | coverInvisible P x}ᶜ) = 1
  simp [measureReal_def, hfull]

theorem deletionVisible_pos_of_uncovered (P : Profile)
    (νD : Measure Profile) [IsFiniteMeasure νD] {k : ℝ}
    (hmass : νD.real Set.univ = k)
    (hinc : ∀ i j : ℕ, (∫ x, x (i + 1, j) ∂νD) =
      (i + 1 : ℝ) * P (i + 1, j))
    (hcorner : P (0, 0) = 0) (huncovered : 0 < ∑' i : ℕ, P (i, 0)) :
    0 < νD.real (deletionVisible P) := by
  by_contra hpos
  have hreal : νD.real (deletionVisible P) = 0 :=
    le_antisymm (le_of_not_gt hpos) measureReal_nonneg
  have hzero : νD (deletionVisible P) = 0 :=
    (measureReal_eq_zero_iff (by finiteness)).mp hreal
  have hrec := recurrence_of_zero_deletionVisible P νD hmass hinc hzero
  have hz : ∀ i : ℕ, P (i, 0) = 0 := by
    intro i
    rw [profile_recurrence_factorization (p := fun i j => P (i, j)) hrec i 0,
      hcorner, mul_zero]
  have hsum : (∑' i : ℕ, P (i, 0)) = 0 := by simp only [hz, tsum_zero]
  rw [hsum] at huncovered
  exact lt_irrefl 0 huncovered

theorem visible_excess_of_cover_saturation (P : Profile)
    (νD νC : Measure Profile) [IsFiniteMeasure νD] [IsProbabilityMeasure νC]
    {k μ : ℝ} (hmass : νD.real Set.univ = k)
    (hinc : ∀ i j : ℕ, (∫ x, x (i + 1, j) ∂νD) =
      (i + 1 : ℝ) * P (i + 1, j))
    (hcorner : P (0, 0) = 0) (huncovered : 0 < ∑' i : ℕ, P (i, 0))
    (hμ : 0 < μ) (hf : Integrable (fun x : Profile => x (0, 1)) νC)
    (hupper : ∀ᵐ x ∂νC, x (0, 1) ≤ μ)
    (hint : (∫ x, x (0, 1) ∂νC) = μ) :
    1 < νD.real (deletionVisible P) + νC.real (coverVisible P) := by
  rw [coverVisible_mass_one P νC hμ hcorner hf hupper hint]
  linarith [deletionVisible_pos_of_uncovered P νD hmass hinc hcorner huncovered]

theorem zero_row_sum_of_coverInvisible (P x : Profile)
    (hP : Summable (fun j : ℕ => P (0, j))) (hx : coverInvisible P x) :
    (∑' j : ℕ, x (0, j)) = ∑' j : ℕ, P (0, j) := by
  have hzero : x (0, 0) = 0 := by simpa using hx 0 0
  have hshift : (fun j : ℕ => x (0, j + 1)) = fun j : ℕ => P (0, j) := by
    funext j
    simpa using hx 0 (j + 1)
  have htail : Summable (fun j : ℕ => x (0, j + 1)) := by rw [hshift]; exact hP
  have hs : Summable (fun j : ℕ => x (0, j)) := (summable_nat_add_iff 1).mp htail
  rw [hs.tsum_eq_zero_add, hzero, zero_add, hshift]

theorem coverVisible_full_of_row_deviation (P : Profile)
    (νC : Measure Profile) {μ lam : ℝ} (hlam : 0 < lam)
    (hP : Summable (fun j : ℕ => P (0, j)))
    (hrow : (∑' j : ℕ, P (0, j)) = μ)
    (hdev : ∀ᵐ x ∂νC, lam ≤ |(∑' j : ℕ, x (0, j)) - μ|) :
    νC.real (coverVisible P) = νC.real Set.univ := by
  have hvisible : ∀ᵐ x ∂νC, x ∈ coverVisible P := by
    filter_upwards [hdev] with x hx
    intro hinvisible
    have heq := zero_row_sum_of_coverInvisible P x hP hinvisible
    rw [heq, hrow, sub_self, abs_zero] at hx
    exact (not_le_of_gt hlam) hx
  have hmeas : νC (coverVisible P) = νC Set.univ := by
    apply measure_congr
    filter_upwards [hvisible] with x hx
    exact propext (iff_true_intro hx)
  exact congrArg ENNReal.toReal hmeas

end ProfileVisibility
end Balanced

end OAI
