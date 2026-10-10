import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Incidence.Affine
import OAI.Combinatorics.BalancedRyser.Incidence.AffineSecondMoment
import OAI.Combinatorics.BalancedRyser.Profiles.MarkedExposure

namespace OAI

open scoped BigOperators
namespace Balanced.CountingExposureKernel
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def uniformSetWeight (s : Finset α) (a : α) : ℝ :=
  if a ∈ s then (s.card : ℝ)⁻¹ else 0

omit [Fintype α] in
theorem uniformSetWeight_nonneg (s : Finset α) (a : α) :
    0 ≤ uniformSetWeight s a := by
  unfold uniformSetWeight
  split_ifs <;> positivity

theorem sum_uniformSetWeight (s : Finset α) (hs : s.Nonempty) :
    ∑ a, uniformSetWeight s a = 1 := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  simp [uniformSetWeight, hc]

omit [Fintype α] in
theorem uniformSetWeight_le (s : Finset α) (a : α) :
    uniformSetWeight s a ≤ (s.card : ℝ)⁻¹ := by
  unfold uniformSetWeight
  split_ifs
  · exact le_rfl
  · positivity

variable {F : Type*} [Fintype F] [DecidableEq F]

def available (used : Finset F) : Finset F := Finset.univ \ used

@[simp] theorem card_available (used : Finset F) :
    (available used).card = Fintype.card F - used.card := by
  simp only [available, Finset.card_sdiff_of_subset (Finset.subset_univ used),
    Finset.card_univ]

def tokenWeight (r : Direction F → ℕ) (used : Direction F → Finset F)
    (l : Line F) : ℝ :=
  (r l.1 : ℝ) / (∑ d, (r d : ℝ)) * uniformSetWeight (available (used l.1)) l.2

theorem tokenWeight_nonneg (r : Direction F → ℕ) (used : Direction F → Finset F)
    (l : Line F) : 0 ≤ tokenWeight r used l := by
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (by simp)))
    (uniformSetWeight_nonneg _ _)

theorem sum_tokenWeight (r : Direction F → ℕ) (used : Direction F → Finset F)
    (hr : 0 < ∑ d, (r d : ℝ))
    (hu : ∀ d, (available (used d)).Nonempty) :
    ∑ l : Line F, tokenWeight r used l = 1 := by
  simp only [tokenWeight, Fintype.sum_prod_type, ← Finset.mul_sum]
  simp only [sum_uniformSetWeight _ (hu _), mul_one, ← Finset.sum_div]
  exact div_self hr.ne'

def tokenPMF (r : Direction F → ℕ) (used : Direction F → Finset F)
    (hr : 0 < ∑ d, (r d : ℝ))
    (hu : ∀ d, (available (used d)).Nonempty) : PMF (Line F) :=
  PMF.ofFintype (fun l => ENNReal.ofReal (tokenWeight r used l)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun l _ => tokenWeight_nonneg r used l),
      sum_tokenWeight r used hr hu, ENNReal.ofReal_one])

@[simp] theorem tokenPMF_real (r : Direction F → ℕ) (used : Direction F → Finset F)
    (hr : 0 < ∑ d, (r d : ℝ))
    (hu : ∀ d, (available (used d)).Nonempty) (l : Line F) :
    (tokenPMF r used hr hu l).toReal = tokenWeight r used l := by
  exact ENNReal.toReal_ofReal (tokenWeight_nonneg r used l)

theorem tokenWeight_le_two_div (r : Direction F → ℕ)
    (used : Direction F → Finset F) (k : ℕ) (η : ℝ)
    (hk : 0 < k) (hη : 0 < η) (hqk : 2 * k ≤ Fintype.card F)
    (hr : ∀ d, r d ≤ k) (hu : ∀ d, (used d).card ≤ k)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ∑ d, (r d : ℝ)) (l : Line F) :
    tokenWeight r used l ≤ 2 / (η * (Fintype.card F : ℝ) ^ 2) := by
  let q : ℝ := Fintype.card F
  have hq : 0 < q := by dsimp [q]; exact_mod_cast (by omega : 0 < Fintype.card F)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkq : k ≤ Fintype.card F := by omega
  have htot : 0 < ∑ d, (r d : ℝ) :=
    lt_of_lt_of_le (mul_pos (mul_pos hη hkR) (by positivity)) hremaining
  have hdir : (r l.1 : ℝ) / (∑ d, (r d : ℝ)) ≤ 1 / (η * q) := by
    apply (div_le_div_iff₀ htot (mul_pos hη hq)).mpr
    have hrR : (r l.1 : ℝ) ≤ k := by exact_mod_cast hr l.1
    have hm := mul_le_mul_of_nonneg_right hrR (mul_nonneg hη.le hq.le)
    dsimp [q] at hm ⊢
    nlinarith [mul_nonneg hη.le hkR.le]
  have hused : (used l.1).card ≤ Fintype.card F := (hu l.1).trans hkq
  have hcard : ((available (used l.1)).card : ℝ) = q - (used l.1).card := by
    rw [card_available, Nat.cast_sub hused]
  have havail : q / 2 ≤ ((available (used l.1)).card : ℝ) := by
    rw [hcard]
    have hx : ((used l.1).card : ℝ) ≤ k := by exact_mod_cast hu l.1
    have hy : 2 * (k : ℝ) ≤ q := by dsimp [q]; exact_mod_cast hqk
    linarith
  have hoff : uniformSetWeight (available (used l.1)) l.2 ≤ 2 / q := by
    calc
      uniformSetWeight (available (used l.1)) l.2 ≤
          ((available (used l.1)).card : ℝ)⁻¹ := uniformSetWeight_le _ _
      _ ≤ 1 / (q / 2) := by
        simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < q / 2) havail
      _ = 2 / q := by ring
  calc
    tokenWeight r used l ≤ (1 / (η * q)) * (2 / q) :=
      mul_le_mul hdir hoff (uniformSetWeight_nonneg _ _) (by positivity)
    _ = 2 / (η * (Fintype.card F : ℝ) ^ 2) := by dsimp [q]; ring

def coverWeight (used : Finset (Line F)) (l : Line F) : ℝ :=
  uniformSetWeight (Finset.univ \ used) l

theorem coverWeight_le_one_div_sq [Nonempty F]
    (used : Finset (Line F)) (hu : used.card ≤ Fintype.card F) (l : Line F) :
    coverWeight used l ≤ 1 / (Fintype.card F : ℝ) ^ 2 := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card F : ℝ) ^ 2 ≤ ((Finset.univ \ used).card : ℝ) := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ used)
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) h
    have huR : (used.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hu
    simp only [Nat.cast_add, Finset.card_univ, Fintype.card_prod,
      Fintype.card_option, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcast
    nlinarith
  calc
    coverWeight used l ≤ ((Finset.univ \ used).card : ℝ)⁻¹ := uniformSetWeight_le _ _
    _ ≤ 1 / (Fintype.card F : ℝ) ^ 2 := by
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hc

theorem cover_available_nonempty [Nonempty F]
    (used : Finset (Line F)) (hu : used.card ≤ Fintype.card F) :
    (Finset.univ \ used).Nonempty := by
  apply Finset.card_pos.mp
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ used)
  have hq := Fintype.card_pos (α := F)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_option] at hc
  nlinarith

theorem sum_coverWeight [Nonempty F]
    (used : Finset (Line F)) (hu : used.card ≤ Fintype.card F) :
    ∑ l : Line F, coverWeight used l = 1 :=
  sum_uniformSetWeight _ (cover_available_nonempty used hu)

variable [Field F]

def markedLines (U : Finset (Point F)) (ε : ℝ) : Finset (Line F) :=
  Finset.univ.filter fun l => ε <
    |(affineIntersectionCount U l : ℝ) / Fintype.card F -
      (U.card : ℝ) / (Fintype.card F : ℝ) ^ 2|

theorem markedLines_eq (U : Finset (Point F)) (ε : ℝ) :
    markedLines U ε = Finset.univ.filter (fun l =>
      ε * Fintype.card F < |(affineIntersectionCount U l : ℝ) -
        (U.card : ℝ) / Fintype.card F|) := by
  apply Finset.filter_congr
  intro l _
  exact MarkedExposure.normalized_deviation_iff _ _ _ _
    (by exact_mod_cast Fintype.card_pos (α := F))

theorem marked_mass_le (U : Finset (Point F)) (ε C : ℝ) (w : Line F → ℝ)
    (hε : 0 < ε) (hC : 0 ≤ C)
    (hw : ∀ l, w l ≤ C / (Fintype.card F : ℝ) ^ 2) :
    (∑ l ∈ markedLines U ε, w l) ≤ C / (4 * ε ^ 2 * Fintype.card F) := by
  rw [markedLines_eq]
  exact MarkedExposure.mass_large_deviations_le Finset.univ
    (fun l => (affineIntersectionCount U l : ℝ)) w
    ((U.card : ℝ) / Fintype.card F) (Fintype.card F) ε C
    (by exact_mod_cast Fintype.card_pos (α := F)) hε hC
    (affineSecondMoment_proof (F := F) U).2.2.2.1 (fun l _ => hw l)

theorem token_marked_mass_le (U : Finset (Point F)) (ε : ℝ)
    (r : Direction F → ℕ) (used : Direction F → Finset F) (k : ℕ) (η : ℝ)
    (hε : 0 < ε) (hk : 0 < k) (hη : 0 < η)
    (hqk : 2 * k ≤ Fintype.card F)
    (hr : ∀ d, r d ≤ k) (hu : ∀ d, (used d).card ≤ k)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ∑ d, (r d : ℝ)) :
    (∑ l ∈ markedLines U ε, tokenWeight r used l) ≤
      (2 / η) / (4 * ε ^ 2 * Fintype.card F) := by
  apply marked_mass_le U ε (2 / η) (tokenWeight r used) hε (by positivity)
  intro l
  simpa only [div_div] using tokenWeight_le_two_div r used k η hk hη hqk hr hu
    hremaining l

theorem cover_marked_mass_le (U : Finset (Point F)) (ε : ℝ)
    (used : Finset (Line F)) (hε : 0 < ε) (hu : used.card ≤ Fintype.card F) :
    (∑ l ∈ markedLines U ε, coverWeight used l) ≤
      1 / (4 * ε ^ 2 * Fintype.card F) := by
  exact marked_mass_le U ε 1 (coverWeight used) hε (by norm_num)
    (coverWeight_le_one_div_sq used hu)

end
end Balanced.CountingExposureKernel

end OAI
