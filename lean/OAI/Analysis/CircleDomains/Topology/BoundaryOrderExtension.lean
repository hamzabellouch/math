import OAI.Analysis.CircleDomains.Topology.BoundaryLiftOrder
import Mathlib.Order.Hom.Set

namespace OAI

/-! Extend the increasing boundary-angle parametrization of the unit
interval to an order isomorphism of the real line. Its outside values
are irrelevant to the boundary pairing. -/

open Set Function

noncomputable section
namespace CircleDomainRigidity

 theorem exists_boundary_orderIso
    (q : ℝ → ℝ) (hq : Continuous q) (hm : StrictMonoOn q (Icc (0 : ℝ) 1))
    (hq0 : q 0 = 0) (hq1 : q 1 = 1) :
    ∃ e : ℝ ≃o ℝ, e 0 = 0 ∧ e 1 = 1 ∧ EqOn e q (Icc (0 : ℝ) 1) := by
  classical
  let f : ℝ → ℝ := fun x => if x < 0 then x else if 1 < x then x else q x
  have hfx {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : f x = q x := by
    simp only [f, ite_eq_right (not_lt.mpr hx.1), ite_eq_right (not_lt.mpr hx.2)]
  have hb {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ q x ∧ q x ≤ 1 := by
    have h0 := hm.monotoneOn (left_mem_Icc.mpr zero_le_one) hx hx.1
    have h1 := hm.monotoneOn hx (right_mem_Icc.mpr zero_le_one) hx.2
    simpa only [hq0, hq1] using And.intro h0 h1
  have hf : StrictMono f := by
    intro x y hxy
    by_cases hx : x < 0
    · by_cases hy : y < 0
      · simpa only [f, ite_eq_left hx, ite_eq_left hy] using hxy
      · by_cases hy1 : 1 < y
        · simpa only [f, ite_eq_left hx, ite_eq_right hy, ite_eq_left hy1] using hxy
        · rw [show f x = x by simp only [f, ite_eq_left hx], hfx ⟨le_of_not_gt hy, le_of_not_gt hy1⟩]
          exact hx.trans_le (hb ⟨le_of_not_gt hy, le_of_not_gt hy1⟩).1
    · by_cases hx1 : 1 < x
      · have hy : ¬ y < 0 := by linarith
        have hy1 : 1 < y := hx1.trans hxy
        simpa only [f, ite_eq_right hx, ite_eq_left hx1, ite_eq_right hy, ite_eq_left hy1] using hxy
      · have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_gt hx, le_of_not_gt hx1⟩
        have hy : ¬ y < 0 := by linarith [hxI.1]
        by_cases hy1 : 1 < y
        · rw [hfx hxI, show f y = y by simp only [f, ite_eq_right hy, ite_eq_left hy1]]
          exact (hb hxI).2.trans_lt hy1
        · have hyI : y ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_gt hy, le_of_not_gt hy1⟩
          rw [hfx hxI, hfx hyI]
          exact hm hxI hyI hxy
  have hs : Surjective f := by
    intro y
    by_cases hy : y < 0
    · exact ⟨y, by simp only [f, ite_eq_left hy]⟩
    · by_cases hy1 : 1 < y
      · exact ⟨y, by simp only [f, ite_eq_right hy, ite_eq_left hy1]⟩
      · obtain ⟨x, hx, hqx⟩ := intermediate_value_Icc zero_le_one hq.continuousOn
          (show y ∈ Icc (q 0) (q 1) by rw [hq0, hq1]; exact ⟨le_of_not_gt hy, le_of_not_gt hy1⟩)
        exact ⟨x, (hfx hx).trans hqx⟩
  let e := hf.orderIsoOfSurjective f hs
  refine ⟨e, ?_, ?_, ?_⟩
  · change f 0 = 0
    rw [hfx (left_mem_Icc.mpr zero_le_one), hq0]
  · change f 1 = 1
    rw [hfx (right_mem_Icc.mpr zero_le_one), hq1]
  · exact fun x hx => hfx hx

end CircleDomainRigidity

end

end OAI
