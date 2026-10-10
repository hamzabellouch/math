import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Deletion.Deletion
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence

namespace OAI

open scoped BigOperators

namespace Balanced.UncoveredExchange

def missed {Point Line : Type*} (A : Finset Point) (D : Finset Line)
    (On : Point → Line → Prop) [DecidableRel On] : Finset Point :=
  A.filter (fun p => ∀ l ∈ D, ¬ On p l)

lemma missed_subset {Point Line : Type*} (A : Finset Point) (D : Finset Line)
    (On : Point → Line → Prop) [DecidableRel On] : missed A D On ⊆ A :=
  Finset.filter_subset _ _

lemma missed_insert {Point Line : Type*} [DecidableEq Line]
    (A : Finset Point) (D : Finset Line) (On : Point → Line → Prop)
    [DecidableRel On] (l : Line) :
    missed A (insert l D) On = (missed A D On).filter (fun p => ¬ On p l) := by
  ext p
  simp [missed, and_left_comm, and_comm]

lemma abs_card_filter_not_sub_le {Point : Type*} (S : Finset Point)
    (P Q : Point → Prop) [DecidablePred P] [DecidablePred Q] :
    |((S.filter (fun p => ¬ P p)).card : ℝ) -
      ((S.filter (fun p => ¬ Q p)).card : ℝ)| ≤
      (S.filter P).card + (S.filter Q).card := by
  have hP : ((S.filter P).card : ℝ) + (S.filter (fun p => ¬ P p)).card = S.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := S) P)
  have hQ : ((S.filter Q).card : ℝ) + (S.filter (fun p => ¬ Q p)).card = S.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := S) Q)
  have hp : (0 : ℝ) ≤ (S.filter P).card := by positivity
  have hq : (0 : ℝ) ≤ (S.filter Q).card := by positivity
  rw [abs_le]
  constructor <;> linarith

theorem missed_exchange_bound {Point Line : Type*} [DecidableEq Line]
    (A : Finset Point) (D : Finset Line) (On : Point → Line → Prop)
    [DecidableRel On] (l m : Line) :
    |((missed A (insert l D) On).card : ℝ) -
      ((missed A (insert m D) On).card : ℝ)| ≤
      (A.filter (fun p => On p l)).card + (A.filter (fun p => On p m)).card := by
  rw [missed_insert, missed_insert]
  apply (abs_card_filter_not_sub_le (missed A D On) (fun p => On p l)
    (fun p => On p m)).trans
  have hl := Finset.card_le_card
    (Finset.filter_subset_filter (fun p => On p l) (missed_subset A D On))
  have hm := Finset.card_le_card
    (Finset.filter_subset_filter (fun p => On p m) (missed_subset A D On))
  exact_mod_cast Nat.add_le_add hl hm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem plane_exchange_bound (D : Finset (Line F)) (l m : Line F) :
    |((uncoveredBy (insert l D)).card : ℝ) -
      ((uncoveredBy (insert m D)).card : ℝ)| ≤ 2 * (Fintype.card F : ℝ) := by
  have h := missed_exchange_bound (Finset.univ : Finset (Point F)) D OnLine l m
  have hm (E : Finset (Line F)) : missed Finset.univ E OnLine = uncoveredBy E := by
    ext p
    simp [missed, uncoveredBy]
  rw [hm, hm] at h
  have hc (a : Line F) : ((Finset.univ : Finset (Point F)).filter
      (fun p => OnLine p a)).card = Fintype.card F := linePoints_card a
  simpa only [hc, two_mul] using h

lemma missed_line (D : Finset (Line F)) (T : Line F) :
    missed (linePoints T) D OnLine = linePoints T ∩ uncoveredBy D := by
  ext p
  simp [missed, uncoveredBy]

theorem target_exchange_bound (D : Finset (Line F)) (T l m : Line F)
    (hl : T ≠ l) (hm : T ≠ m) :
    |((linePoints T ∩ uncoveredBy (insert l D)).card : ℝ) -
      ((linePoints T ∩ uncoveredBy (insert m D)).card : ℝ)| ≤ 2 := by
  have h := missed_exchange_bound (linePoints T) D OnLine l m
  have heq (a : Line F) : (linePoints T).filter (fun p => OnLine p a) =
      linePoints T ∩ linePoints a := by
    ext p
    simp [linePoints]
  rw [missed_line, missed_line, heq l, heq m] at h
  have hlc : ((linePoints T ∩ linePoints l).card : ℝ) ≤ 1 := by
    exact_mod_cast linePoints_inter_card_le_one T l hl
  have hmc : ((linePoints T ∩ linePoints m).card : ℝ) ≤ 1 := by
    exact_mod_cast linePoints_inter_card_le_one T m hm
  linarith

theorem normalized_plane_exchange_bound (D : Finset (Line F)) (l m : Line F) :
    |((uncoveredBy (insert l D)).card : ℝ) / (Fintype.card F : ℝ)^2 -
      ((uncoveredBy (insert m D)).card : ℝ) / (Fintype.card F : ℝ)^2| ≤
      2 / (Fintype.card F : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by positivity
  rw [← sub_div, abs_div, abs_of_nonneg (sq_nonneg (Fintype.card F : ℝ))]
  calc
    _ ≤ (2 * (Fintype.card F : ℝ)) / (Fintype.card F : ℝ)^2 :=
      div_le_div_of_nonneg_right (plane_exchange_bound D l m) (sq_nonneg _)
    _ = 2 / (Fintype.card F : ℝ) := by field_simp

theorem normalized_target_exchange_bound (D : Finset (Line F)) (T l m : Line F)
    (hl : T ≠ l) (hm : T ≠ m) :
    |((linePoints T ∩ uncoveredBy (insert l D)).card : ℝ) / (Fintype.card F : ℝ) -
      ((linePoints T ∩ uncoveredBy (insert m D)).card : ℝ) / (Fintype.card F : ℝ)| ≤
      2 / (Fintype.card F : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by positivity
  rw [← sub_div, abs_div, abs_of_pos hq]
  exact div_le_div_of_nonneg_right (target_exchange_bound D T l m hl hm) hq.le

end Balanced.UncoveredExchange

end OAI
