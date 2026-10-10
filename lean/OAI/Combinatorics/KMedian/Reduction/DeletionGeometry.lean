import Mathlib
import OAI.Combinatorics.KMedian.Model
import OAI.Combinatorics.KMedian.Instance

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance deletionGeometryPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

structure Serving (U : Finset (Fin I.n)) where
  assignment : ↥I.clients → ↥U
  assignment_cost : ∀ j, dist j.val (assignment j).val=nearest I j U
  other : ↥U → ↥U
  other_ne : ∀ t, other t ≠ t
  other_nearest : ∀ t u, u ≠ t → dist t.val (other t).val ≤ dist t.val u.val

theorem serving_exists (U : Finset (Fin I.n)) (hk : I.k < U.card) :
    Nonempty (Serving (I:=I) U) := by
  classical
  have hU : U.Nonempty := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hk)
  have has : ∀ j : ↥I.clients, ∃ u : ↥U, dist j.val u.val=nearest I j U := by
    intro j
    obtain ⟨u,hu,he⟩ := I.nearest_attained j U hU
    exact ⟨⟨u,hu⟩,he.symm⟩
  choose a ha using has
  have hot : ∀ t : ↥U, ∃ u : ↥U, u ≠ t ∧ ∀ v : ↥U, v ≠ t → dist t.val u.val ≤ dist t.val v.val := by
    intro t
    have hE : (U.erase t.val).Nonempty := by
      apply card_pos.mp
      rw [card_erase_of_mem t.property]
      have hkp := I.k_pos
      omega
    obtain ⟨u,hu,he⟩ := I.nearest_attained t (U.erase t.val) hE
    refine ⟨⟨u,(mem_erase.mp hu).2⟩,?_,?_⟩
    · intro hh
      exact (mem_erase.mp hu).1 (congrArg Subtype.val hh)
    · intro v hv
      have hv' : v.val ≠ t.val := fun hh => hv (Subtype.ext hh)
      have hb := I.nearest_le t (mem_erase.mpr ⟨hv',v.property⟩)
      rw [he] at hb
      exact hb
  choose other hne hnear using hot
  exact ⟨⟨a,ha,other,hne,hnear⟩⟩

namespace Serving
variable {U : Finset (Fin I.n)}

def radius (D : Serving (I:=I) U) (t : ↥U) : ℝ := dist t.val (D.other t).val

theorem radius_nonneg (D : Serving (I:=I) U) (t : ↥U) : 0 ≤ D.radius t := dist_nonneg

theorem radius_pos (D : Serving (I:=I) U) (t : ↥U) : 0 < D.radius t := by
  apply lt_of_le_of_ne (D.radius_nonneg t)
  intro he
  change (0:ℝ)=(I.distance t.val (D.other t).val:ℝ) at he
  have hr : I.distance t.val (D.other t).val=0 := by exact_mod_cast he.symm
  have heq := (I.distance_eq_zero _ _).mp hr
  exact D.other_ne t (Subtype.ext heq.symm)

noncomputable def group (D : Serving (I:=I) U) (t : ↥U) : Finset ↥I.clients :=
  univ.filter (fun j => D.assignment j=t)

noncomputable def groupCost (D : Serving (I:=I) U) (t : ↥U) : ℝ :=
  ∑ j ∈ D.group t, nearest I j U

theorem groupCost_nonneg (D : Serving (I:=I) U) (t : ↥U) : 0 ≤ D.groupCost t :=
  sum_nonneg (fun j _ => I.nearest_nonneg j U)

theorem groupCost_total (D : Serving (I:=I) U) : ∑ t, D.groupCost t=cost I U := by
  change (∑ t : ↥U, ∑ j with D.assignment j=t, nearest I j U)=cost I U
  calc
    _ = ∑ j : ↥I.clients, nearest I j U := sum_fiberwise univ D.assignment (fun j => nearest I j U)
    _ = cost I U := sum_coe_sort I.clients (fun j => nearest I j U)

theorem deletion_bound (D : Serving (I:=I) U) (t : ↥U) :
    cost I (U.erase t.val)-cost I U ≤ (D.group t).card*D.radius t := by
  have hpoint : ∀ j : ↥I.clients, nearest I j (U.erase t.val)-nearest I j U ≤
      if D.assignment j=t then D.radius t else 0 := by
    intro j
    by_cases hj : D.assignment j=t
    · rw [ite_eq_left hj]
      have ho : (D.other t).val ∈ U.erase t.val := by
        apply mem_erase.mpr
        exact ⟨fun he => D.other_ne t (Subtype.ext he),(D.other t).property⟩
      have hnear := I.nearest_le j ho
      have htri := dist_triangle j.val t.val (D.other t).val
      have hex : dist j.val t.val=nearest I j U := by simpa only [hj] using D.assignment_cost j
      change nearest I j (U.erase t.val) ≤ dist j.val (D.other t).val at hnear
      dsimp only [radius]
      linarith only [hnear,htri,hex]
    · rw [ite_eq_right hj]
      have ha : (D.assignment j).val ∈ U.erase t.val := by
        exact mem_erase.mpr ⟨fun he => hj (Subtype.ext he),(D.assignment j).property⟩
      have hnear := I.nearest_le j ha
      change nearest I j (U.erase t.val) ≤ dist j.val (D.assignment j).val at hnear
      rw [D.assignment_cost j] at hnear
      linarith only [hnear]
  calc
    cost I (U.erase t.val)-cost I U = ∑ j : ↥I.clients,
        (nearest I j (U.erase t.val)-nearest I j U) := by
          rw [sum_sub_distrib]
          rw [sum_coe_sort I.clients (fun j => nearest I j (U.erase t.val)),
            sum_coe_sort I.clients (fun j => nearest I j U)]
          rfl
    _ ≤ ∑ j : ↥I.clients, if D.assignment j=t then D.radius t else 0 :=
      sum_le_sum (fun j _ => hpoint j)
    _ = (D.group t).card*D.radius t := by
      rw [← sum_filter]
      simp only [group,sum_const,nsmul_eq_mul]

end Serving
end MetricKMedian.Reduction
end
end

end OAI
