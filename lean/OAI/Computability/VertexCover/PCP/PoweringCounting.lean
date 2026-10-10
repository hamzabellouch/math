import Mathlib
import OAI.Computability.VertexCover.PCP.PoweringAddresses
import OAI.Computability.VertexCover.PCP.PoweringTest

namespace OAI

                                                                                         

namespace UniqueGames.Foundations.PCP.PoweringCounting

open PoweringWalks PoweringLabels PoweringTest
open scoped BigOperators

variable {V D A E : Type*}

theorem constraint_rejection_mean_eq_count [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A) :
    SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) =
      (H.rejectionCount labels : ℝ) / (Fintype.card E : ℝ) := by
  classical
  rw [SpectralReturn.mean_eq_sum_div_card]
  simp only [PoweringMoment.bit, ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]
  apply congrArg (fun x : ℝ => x / (Fintype.card E : ℝ))
  convert (Finset.sum_boole (R := ℝ)
    (fun e => H.edgeSatisfied labels e = false) Finset.univ) using 1 ; try rfl
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : H.edgeSatisfied labels e = false <;> simp [h]

theorem constraint_rejection_lower_iff [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A)
    (hcard : 0 < Fintype.card E) (ε : ℝ) :
    ε ≤ SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) ↔
      ε * (Fintype.card E : ℝ) ≤ (H.rejectionCount labels : ℝ) := by
  rw [constraint_rejection_mean_eq_count]
  exact le_div_iff₀ (Nat.cast_pos.mpr hcard)

theorem edgeDensity_eq_bit_mean [Fintype V] [Fintype D]
    (bad : Edge V D → Bool) :
    SpectralReturn.edgeDensity bad =
      SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit (bad e = true)) := by
  convert (SpectralReturn.mean_prod
    (fun e : Edge V D => PoweringMoment.bit (bad e = true))).symm using 1 ; try rfl
  change SpectralReturn.mean (fun v => SpectralReturn.mean
    (fun d => if bad (v, d) then (1 : ℝ) else 0)) = _
  apply congrArg SpectralReturn.mean
  funext v
  apply congrArg SpectralReturn.mean
  funext d
  cases h : bad (v, d) <;> simp [PoweringMoment.bit]

theorem base_edgeDensity_eq_rejection_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) :
    SpectralReturn.edgeDensity (decodedBad G accepts assignment) =
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ) /
        (Fintype.card (Edge V D) : ℝ) := by
  calc
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        (decodedBad G accepts assignment e = true)) := edgeDensity_eq_bit_mean _
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        ((baseGraph G accepts reverse_accepts).edgeSatisfied assignment e = false)) := by
      apply congrArg SpectralReturn.mean
      funext e
      exact congrArg PoweringMoment.bit
        (propext (decodedBad_eq_true_iff G accepts assignment e))
    _ = _ := constraint_rejection_mean_eq_count _ _

theorem base_count_lower_to_density [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (hcard : 0 < Fintype.card (Edge V D)) (ε : ℝ)
    (hcount : ε * (Fintype.card (Edge V D) : ℝ) ≤
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ)) :
    ε ≤ SpectralReturn.edgeDensity (decodedBad G accepts assignment) := by
  rw [base_edgeDensity_eq_rejection_count G accepts reverse_accepts assignment]
  exact (le_div_iff₀ (Nat.cast_pos.mpr hcard)).2 hcount

theorem powered_rejection_mean_eq_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) :
    SpectralReturn.mean (fun d : Dart V D n => PoweringMoment.bit
      ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false)) =
      ((poweredGraph G accepts n selectors).rejectionCount labels : ℝ) /
        (Fintype.card (Dart V D n) : ℝ) :=
  constraint_rejection_mean_eq_count _ _

theorem path_rejection_mean_eq_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) :
    SpectralReturn.mean (fun w : Walk V D (n + 1) => PoweringMoment.bit
      (pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false)) =
      ((poweredGraph G accepts n selectors).rejectionCount labels : ℝ) /
        (Fintype.card (Dart V D n) : ℝ) := by
  rw [← rejection_mean_eq_path_mean G accepts n selectors labels]
  exact powered_rejection_mean_eq_count G accepts n selectors labels

theorem powered_density_lower_to_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A)
    (hcard : 0 < Fintype.card (Dart V D n)) (ε : ℝ)
    (hlower : ε ≤ SpectralReturn.mean (fun w : Walk V D (n + 1) => PoweringMoment.bit
      (pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false))) :
    ε * (Fintype.card (Dart V D n) : ℝ) ≤
      ((poweredGraph G accepts n selectors).rejectionCount labels : ℝ) := by
  rw [path_rejection_mean_eq_count G accepts n selectors labels] at hlower
  exact (le_div_iff₀ (Nat.cast_pos.mpr hcard)).1 hlower

theorem natCard_dart [Finite V] [Finite D] (n : Nat) :
    Nat.card (Dart V D n) = 2 * Nat.card V * Nat.card D ^ (n + 1) := by
  simp [Dart, Walk, Nat.card_prod, Nat.card_fun, Nat.mul_assoc]

theorem fintypeCard_dart [Fintype V] [Fintype D] (n : Nat) :
    Fintype.card (Dart V D n) =
      2 * Fintype.card V * Fintype.card D ^ (n + 1) := by
  simpa only [Nat.card_eq_fintype_card] using (natCard_dart (V := V) (D := D) n)

theorem natCard_poweredAlphabet [Finite D] [Finite A] (n : Nat) :
    Nat.card (PaddedLabel D (n + 1) A) =
      Nat.card A ^ (∑ j : Fin (n + 2), Nat.card D ^ j.val) :=
  PoweringLabels.card_paddedLabel (n + 1)

theorem natCard_finitePortAlphabet [Finite A] (d n : Nat) :
    Nat.card (PaddedLabel (Fin d) (n + 1) A) =
      Nat.card A ^ (PoweringAddresses.allAddresses d (n + 1)).length := by
  rw [PoweringLabels.card_paddedLabel, PoweringAddresses.length_allAddresses]
  simp only [Nat.card_fin]

end UniqueGames.Foundations.PCP.PoweringCounting

end OAI
