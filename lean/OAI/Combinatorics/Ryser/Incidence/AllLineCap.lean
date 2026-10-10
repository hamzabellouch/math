import OAI.Combinatorics.Ryser.Incidence.PruningCore
import OAI.Combinatorics.Ryser.Geometry.ProjectiveJoins

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Incidence

variable {Pt Ln : Type*} [instDecidableEqPt : DecidableEq Pt] [DecidableEq Ln]

theorem leftDegree_le_erase_add_one (R : Pt → Ln → Prop) (L : Finset Ln)
    (p : Pt) (l : Ln) : leftDegree R L p ≤ leftDegree R (L.erase l) p + 1 := let _ := instDecidableEqPt; by
  classical
  apply (Finset.card_le_card (show L.filter (R p) ⊆
      insert l ((L.erase l).filter (R p)) from ?_)).trans (Finset.card_insert_le _ _)
  intro m hm
  obtain ⟨hmL, hpm⟩ := Finset.mem_filter.mp hm
  apply Finset.mem_insert.mpr
  by_cases he : m = l
  · exact Or.inl he
  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨he, hmL⟩, hpm⟩)

theorem rightDegree_mul_sub_one_le (R : Pt → Ln → Prop) (P : Finset Pt)
    (L : Finset Ln) {d : ℝ}
    (hmin : ∀ p ∈ P, d ≤ (leftDegree R L p : ℝ))
    (huniq : ∀ l m : Ln, l ≠ m → ∀ p q : Pt,
      R p l → R p m → R q l → R q m → p = q) (l : Ln) :
    (rightDegree R P l : ℝ) * (d - 1) ≤ (L.card : ℝ) := by
  classical
  let Q := P.filter (fun p => R p l)
  have hupper : incidenceCount R Q (L.erase l) ≤ L.card := by
    calc
      incidenceCount R Q (L.erase l) =
          incidenceCount (fun l p => R p l) (L.erase l) Q := incidenceCount_swap R Q _
      _ ≤ ∑ m ∈ L.erase l, 1 := by
        apply Finset.sum_le_sum
        intro m hm
        change (Q.filter (fun p => R p m)).card ≤ 1
        apply Finset.card_le_one.mpr
        intro p hp q hq
        obtain ⟨hpQ, hpm⟩ := Finset.mem_filter.mp hp
        obtain ⟨hqQ, hqm⟩ := Finset.mem_filter.mp hq
        exact huniq m l (Finset.mem_erase.mp hm).1 p q hpm
          (Finset.mem_filter.mp hpQ).2 hqm (Finset.mem_filter.mp hqQ).2
      _ = (L.erase l).card := by simp
      _ ≤ L.card := Finset.card_erase_le
  have hlower : (Q.card : ℝ) * (d - 1) ≤ (incidenceCount R Q (L.erase l) : ℝ) := by
    calc
      (Q.card : ℝ) * (d - 1) = ∑ p ∈ Q, (d - 1) := by simp [mul_sub]
      _ ≤ ∑ p ∈ Q, (leftDegree R (L.erase l) p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hdegree := hmin p (Finset.mem_filter.mp hp).1
        have hdelete : (leftDegree R L p : ℝ) ≤
            (leftDegree R (L.erase l) p : ℝ) + 1 := by
          exact_mod_cast leftDegree_le_erase_add_one R L p l
        linarith
      _ = (incidenceCount R Q (L.erase l) : ℝ) := by
        simp only [incidenceCount, Nat.cast_sum]
  have hupper' : (incidenceCount R Q (L.erase l) : ℝ) ≤ (L.card : ℝ) := by
    exact_mod_cast hupper
  exact hlower.trans hupper'

theorem rightDegree_le_div_sub_one (R : Pt → Ln → Prop) (P : Finset Pt)
    (L : Finset Ln) {d : ℝ} (hd : 1 < d)
    (hmin : ∀ p ∈ P, d ≤ (leftDegree R L p : ℝ))
    (huniq : ∀ l m : Ln, l ≠ m → ∀ p q : Pt,
      R p l → R p m → R q l → R q m → p = q) (l : Ln) :
    (rightDegree R P l : ℝ) ≤ (L.card : ℝ) / (d - 1) :=
  (le_div_iff₀ (sub_pos.mpr hd)).2 (rightDegree_mul_sub_one_le R P L hmin huniq l)

variable {F : Type*} [Field F] [DecidableEq F]

theorem projective_all_line_cap (P : Finset (ProjectivePoint F))
    (L : Finset (ProjectiveLine F)) {d : ℝ} (hd : 1 < d)
    (hmin : ∀ p ∈ P, d ≤ (leftDegree ProjectiveIncidence L p : ℝ))
    (l : ProjectiveLine F) :
    (rightDegree ProjectiveIncidence P l : ℝ) ≤ (L.card : ℝ) / (d - 1) := by
  apply rightDegree_le_div_sub_one ProjectiveIncidence P L hd hmin
  intro l m hlm p q hpl hpm hql hqm
  exact eq_projectivePoint_of_common_incidence hlm hpl hpm hql hqm

end RyserCoveringCounterexample.Incidence

end

end OAI
