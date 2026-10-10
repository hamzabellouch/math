import OAI.Analysis.CircleDomains.Selection.ResidualConstraints
import Mathlib.Topology.Instances.Rat

namespace OAI

/-! Every open time interval is the directed union of the rational closed
intervals contained in it. This passes the coded constraints to open pieces. -/

open Set

noncomputable section

namespace CircleDomainRigidity

theorem rationalTime_toTime_monotone : Monotone RationalPathTime.toTime := by
  intro a b hab
  change (a.val : ℝ) ≤ (b.val : ℝ)
  exact_mod_cast hab

theorem rationalTime_toTime_min (a b : RationalPathTime) :
    (min a b).toTime = min a.toTime b.toTime := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (rationalTime_toTime_monotone h)]
  · rw [min_eq_right h, min_eq_right (rationalTime_toTime_monotone h)]

theorem rationalTime_toTime_max (a b : RationalPathTime) :
    (max a b).toTime = max a.toTime b.toTime := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (rationalTime_toTime_monotone h)]
  · rw [max_eq_left h, max_eq_left (rationalTime_toTime_monotone h)]

def InnerRationalInterval (a b : PathTime) :=
  {p : RationalPathTime × RationalPathTime | a < p.1.toTime ∧ p.2.toTime < b}

def innerRationalInterval (a b : PathTime) (p : InnerRationalInterval a b) : Set PathTime :=
  Icc p.val.1.toTime p.val.2.toTime

theorem innerRationalInterval_directed (a b : PathTime) :
    Directed (· ⊆ ·) (innerRationalInterval a b) := by
  intro p q
  let r : InnerRationalInterval a b := ⟨(min p.val.1 q.val.1, max p.val.2 q.val.2), by
    change a < (min p.val.1 q.val.1).toTime ∧ (max p.val.2 q.val.2).toTime < b
    simp only [rationalTime_toTime_min, rationalTime_toTime_max, lt_min_iff, max_lt_iff]
    exact ⟨⟨p.property.1, q.property.1⟩, ⟨p.property.2, q.property.2⟩⟩⟩
  refine ⟨r, ?_, ?_⟩
  · exact Icc_subset_Icc (rationalTime_toTime_monotone (min_le_left _ _))
      (rationalTime_toTime_monotone (le_max_left _ _))
  · exact Icc_subset_Icc (rationalTime_toTime_monotone (min_le_right _ _))
      (rationalTime_toTime_monotone (le_max_right _ _))

theorem iUnion_innerRationalInterval (a b : PathTime) :
    (⋃ p : InnerRationalInterval a b, innerRationalInterval a b p) = Ioo a b := by
  ext t
  constructor
  · intro ht
    obtain ⟨p, hp⟩ := mem_iUnion.mp ht
    exact ⟨p.property.1.trans_le hp.1, hp.2.trans_lt p.property.2⟩
  · intro ht
    obtain ⟨q, haq, hqt⟩ := exists_rat_btwn (show (a : ℝ) < (t : ℝ) from ht.1)
    obtain ⟨r, htr, hrb⟩ := exists_rat_btwn (show (t : ℝ) < (b : ℝ) from ht.2)
    have hq : q ∈ Icc (0 : ℚ) 1 := by
      constructor
      · exact_mod_cast a.property.1.trans haq.le
      · exact_mod_cast hqt.le.trans t.property.2
    have hr : r ∈ Icc (0 : ℚ) 1 := by
      constructor
      · exact_mod_cast t.property.1.trans htr.le
      · exact_mod_cast hrb.le.trans b.property.2
    let p : InnerRationalInterval a b := ⟨(⟨q, hq⟩, ⟨r, hr⟩), ⟨haq, hrb⟩⟩
    exact mem_iUnion.mpr ⟨p, hqt.le, htr.le⟩

end CircleDomainRigidity

end

end OAI
