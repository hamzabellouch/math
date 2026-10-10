import OAI.Geometry.HeilbronnTriangle.EqualCoordinatePlane
import OAI.Geometry.HeilbronnTriangle.AuxiliaryAffineWeights

namespace OAI


noncomputable section
namespace Problem355.ZeroThreeCasePartition

open scoped BigOperators
open PlaneFunctional

variable {K V : Type*} [Field K]

theorem eq_zero_of_parallel_differences (x : Fin 3 → K)
    (h01 : ∃ a : K, x = a • coordinateDifference (0 : Fin 3) 1)
    (h02 : ∃ a : K, x = a • coordinateDifference (0 : Fin 3) 2) : x = 0 := by
  obtain ⟨a, ha⟩ := h01
  obtain ⟨b, hb⟩ := h02
  have h1 := congrFun (ha.symm.trans hb) 1
  have ha0 : a = 0 := by
    simpa [coordinateDifference, Pi.smul_apply] using h1
  simpa [ha0] using ha

theorem exists_nonspecial_pair (x : Fin 3 → K) (hx : x ≠ 0) :
    ∃ i j : Fin 3, i < j ∧ ¬ ∃ a : K, x = a • coordinateDifference i j := by
  classical
  by_cases h01 : ∃ a : K, x = a • coordinateDifference (0 : Fin 3) 1
  · refine ⟨0, 2, by decide, ?_⟩
    intro h02
    exact hx (eq_zero_of_parallel_differences x h01 h02)
  · exact ⟨0, 1, by decide, h01⟩

def Additional (x : Fin 3 → K) (p : Fin 3 → V) (i j : Fin 3) : Prop :=
  i < j ∧ p i = p j ∧ ¬ ∃ a : K, x = a • coordinateDifference i j

def SpecialDistinct (x : Fin 3 → K) (p : Fin 3 → V) (i j : Fin 3) : Prop :=
  i < j ∧ p i = p j ∧ (∃ a : K, x = a • coordinateDifference i j) ∧
    ∃ u v : Fin 3, p u ≠ p v

theorem additional_of_all_equal (x : Fin 3 → K) (hx : x ≠ 0)
    (p : Fin 3 → V) (hp : ∀ i j, p i = p j) :
    ∃ i j : Fin 3, Additional x p i j := by
  obtain ⟨i, j, hij, hn⟩ := exists_nonspecial_pair x hx
  exact ⟨i, j, hij, hp i j, hn⟩

theorem repeated_pair_cover (x : Fin 3 → K) (hx : x ≠ 0) (p : Fin 3 → V)
    (hp : ∃ i j : Fin 3, i ≠ j ∧ p i = p j) :
    (∃ i j : Fin 3, Additional x p i j) ∨
      ∃ i j : Fin 3, SpecialDistinct x p i j := by
  classical
  by_cases hadd : ∃ i j : Fin 3, Additional x p i j
  · exact Or.inl hadd
  right
  obtain ⟨i, j, hij, heq⟩ := hp
  have hordered : ∃ i j : Fin 3, i < j ∧ p i = p j := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨i, j, hlt, heq⟩
    · exact ⟨j, i, hgt, heq.symm⟩
  obtain ⟨i, j, hij, heq⟩ := hordered
  have hspecial : ∃ a : K, x = a • coordinateDifference i j := by
    by_contra hn
    exact hadd ⟨i, j, hij, heq, hn⟩
  refine ⟨i, j, hij, heq, hspecial, ?_⟩
  by_contra hn
  have hall : ∀ u v : Fin 3, p u = p v := by
    intro u v
    by_contra huv
    exact hn ⟨u, v, huv⟩
  exact hadd (additional_of_all_equal x hx p hall)

theorem support_cover [AddCommGroup V] [Module K V]
    (x : Fin 3 → K) (hx : x ≠ 0) (p : Fin 3 → V)
    (hp : AffineIndependent K p ∨ ∃ i j : Fin 3, i ≠ j ∧ p i = p j) :
    AffineIndependent K p ∨ (∃ i j : Fin 3, Additional x p i j) ∨
      ∃ i j : Fin 3, SpecialDistinct x p i j := by
  rcases hp with hp | hp
  · exact Or.inl hp
  · exact Or.inr (repeated_pair_cover x hx p hp)

end Problem355.ZeroThreeCasePartition

end

end OAI
