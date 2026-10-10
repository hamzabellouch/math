import OAI.Analysis.LipschitzHilbert.Geometry.SeparatedPacking
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI

/-!
# Marked mass shells

The shell estimate and weighted sum of §10, `res:marked-shell-count` and
`res:marked-weight-sum`. A positive drop at every marked index makes the
corresponding masses separated. We use shells of ratio four, grouping
pairs of the manuscript's dyadic shells, so that the geometric ratio is
at most one half throughout the required exponent range.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

theorem marked_mass_separated (n : ℕ → ℝ) (hn : Antitone n)
    (S : Finset ℕ) {c : ℝ} (hdrop : ∀ i ∈ S, c ≤ n i - n (i + 1)) :
    Separated (fun i : S => n i) c := by
  intro i j hij
  have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstep := hdrop i i.property
    have horder := hn (show i.val + 1 ≤ j.val by omega)
    have hmono := hn hlt.le
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    linarith
  · have hstep := hdrop j j.property
    have horder := hn (show j.val + 1 ≤ i.val by omega)
    have hmono := hn hgt.le
    rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
    linarith

theorem separated_shell_card {ι : Type*} [Fintype ι] (mass : ι → ℝ)
    {c t b : ℝ} (hc : 0 < c) (htb : t ≤ b)
    (hsep : Separated mass c) (S : Finset ι)
    (hS : ∀ i ∈ S, t ≤ mass i ∧ mass i ≤ b) :
    (S.card : ℝ) ≤ 1 + (b - t) / c := by
  classical
  have hs : Separated (fun i : S => mass i) c := by
    intro i j hij
    exact hsep (fun h => hij (Subtype.ext h))
  simpa only [Fintype.card_coe] using
    separated_card_le_span (fun i : S => mass i) hc htb hs (fun i => hS i i.property)

private theorem four_rpow_le_half {q : ℝ} (hq : q ≤ -(1 / 2 : ℝ)) :
    (4 : ℝ) ^ q ≤ 1 / 2 := by
  have h : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hq).trans_eq h

/-- A separated finite family above `M` has a summable negative-power
weight, uniformly in its cardinality and its largest mass. -/
theorem separated_negative_power_sum {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) {c M e : ℝ} (hc : 0 < c) (hM : 1 ≤ M)
    (he : e ≤ -(3 / 2 : ℝ)) (hsep : Separated mass c)
    (hmass : ∀ i, M ≤ mass i) :
    (∑ i, mass i ^ e) ≤ 2 * (1 + 3 / c) * M ^ (e + 1) := by
  classical
  have hM0 : 0 < M := by linarith
  have he0 : e ≤ 0 := by linarith
  have hq : e + 1 ≤ -(1 / 2 : ℝ) := by linarith
  have hex (i : ι) : ∃ r : ℕ, (4 : ℝ) ^ r * M ≤ mass i ∧
      mass i < 4 * ((4 : ℝ) ^ r * M) := by
    obtain ⟨r, hr, hr'⟩ := exists_nat_pow_near
      ((one_le_div hM0).mpr (hmass i)) (by norm_num : (1 : ℝ) < 4)
    refine ⟨r, (le_div_iff₀ hM0).mp hr, ?_⟩
    have h := (div_lt_iff₀ hM0).mp hr'
    rw [pow_succ] at h
    nlinarith
  choose shell hshell using hex
  let R : Finset ℕ := Finset.univ.image shell
  have hR (i : ι) : shell i ∈ R := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hshell_bound (r : ℕ) :
      (∑ i ∈ Finset.univ.filter (fun i => shell i = r), mass i ^ e) ≤
        (1 + 3 / c) * M ^ (e + 1) * (1 / 2 : ℝ) ^ r := by
    let t : ℝ := (4 : ℝ) ^ r * M
    have ht0 : 0 < t := mul_pos (pow_pos (by norm_num) _) hM0
    have ht1 : 1 ≤ t := by
      have hp : (1 : ℝ) ≤ 4 ^ r := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)
      dsimp [t]
      nlinarith
    have hcard := separated_shell_card mass hc (show t ≤ 4 * t by linarith) hsep
      (Finset.univ.filter (fun i => shell i = r)) (by
        intro i hi
        have hi' : shell i = r := (Finset.mem_filter.mp hi).2
        change (4 : ℝ) ^ r * M ≤ mass i ∧ mass i ≤ 4 * ((4 : ℝ) ^ r * M)
        constructor
        · simpa only [hi'] using (hshell i).1
        · simpa only [hi'] using (hshell i).2.le)
    have hcard' : ((Finset.univ.filter (fun i => shell i = r)).card : ℝ) ≤
        (1 + 3 / c) * t := by
      have hc0 : 0 ≤ 3 / c := by positivity
      have hcalc : 1 + (4 * t - t) / c ≤ (1 + 3 / c) * t := by
        have heq : 1 + (4 * t - t) / c = 1 + (3 / c) * t := by ring
        rw [heq]
        nlinarith
      exact hcard.trans hcalc
    calc
      _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => shell i = r), t ^ e := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := (Finset.mem_filter.mp hi).2
        exact Real.rpow_le_rpow_of_nonpos ht0 (by simpa [t, hi'] using (hshell i).1) he0
      _ = ((Finset.univ.filter (fun i => shell i = r)).card : ℝ) * t ^ e := by simp
      _ ≤ ((1 + 3 / c) * t) * t ^ e :=
        mul_le_mul_of_nonneg_right hcard' (Real.rpow_nonneg ht0.le _)
      _ = (1 + 3 / c) * M ^ (e + 1) * ((4 : ℝ) ^ (e + 1)) ^ r := by
        rw [show ((1 + 3 / c) * t) * t ^ e = (1 + 3 / c) * t ^ (e + 1) by
          rw [Real.rpow_add_one ht0.ne']; ring]
        dsimp [t]
        rw [Real.mul_rpow (by positivity) hM0.le, ← Real.rpow_pow_comm (by norm_num)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) (four_rpow_le_half hq) r)
        (by positivity)
  calc
    _ = ∑ r ∈ R, ∑ i ∈ Finset.univ.filter (fun i => shell i = r), mass i ^ e :=
      (Finset.sum_fiberwise_of_maps_to (fun i _ => hR i) _).symm
    _ ≤ ∑ r ∈ R, (1 + 3 / c) * M ^ (e + 1) * (1 / 2 : ℝ) ^ r :=
      Finset.sum_le_sum fun r _ => hshell_bound r
    _ = ((1 + 3 / c) * M ^ (e + 1)) * ∑ r ∈ R, (1 / 2 : ℝ) ^ r :=
      (Finset.mul_sum ..).symm
    _ ≤ ((1 + 3 / c) * M ^ (e + 1)) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (summable_geometric_two.sum_le_tsum R (fun r _ => by positivity)).trans_eq
        tsum_geometric_two
    _ = _ := by ring

/-- The manuscript's marked weight bound follows from the actual
positive mass drops, with an explicit constant depending only on `c`. -/
theorem marked_weight_sum (n : ℕ → ℝ) (hn : Antitone n) (S : Finset ℕ)
    {c M μ : ℝ} (hc : 0 < c) (hM : 1 ≤ M) (hμ : μ ≤ 1 / 12)
    (hdrop : ∀ i ∈ S, c ≤ n i - n (i + 1)) (hmass : ∀ i ∈ S, M ≤ n i) :
    (∑ i ∈ S, n i ^ (-2 + 2 * μ)) ≤
      2 * (1 + 3 / c) * M ^ (-1 + 2 * μ) := by
  have h := separated_negative_power_sum (fun i : S => n i) hc hM
    (show -2 + 2 * μ ≤ -(3 / 2 : ℝ) by linarith)
    (marked_mass_separated n hn S hdrop) (fun i => hmass i i.property)
  rw [← Finset.sum_coe_sort S (fun i => n i ^ (-2 + 2 * μ))]
  simpa only [show -2 + 2 * μ + 1 = -1 + 2 * μ by ring] using h

end LipschitzHilbert

end

end OAI
