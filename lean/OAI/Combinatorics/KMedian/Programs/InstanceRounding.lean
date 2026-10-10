import Mathlib
import OAI.Combinatorics.KMedian.Instance
import OAI.Combinatorics.KMedian.Probability.NonnegativeRounding

namespace OAI

section
section
namespace MetricKMedian
open Finset

structure FractionalSolution (I : Instance) where
  opening : ↥I.facilities → ℚ
  assignment : ↥I.clients → ↥I.facilities → ℚ
  opening_nonneg : ∀ i, 0 ≤ opening i
  opening_le_one : ∀ i, opening i ≤ 1
  assignment_nonneg : ∀ j i, 0 ≤ assignment j i
  assignment_le_opening : ∀ j i, assignment j i ≤ opening i
  assignment_total : ∀ j, ∑ i, assignment j i=1
  opening_budget : ∑ i, opening i ≤ I.k

namespace FractionalSolution

def value {I : Instance} (s : FractionalSolution I) : ℚ :=
  ∑ j, ∑ i, s.assignment j i*I.distance j.val i.val

theorem value_nonneg {I : Instance} (s : FractionalSolution I) : 0 ≤ s.value :=
  sum_nonneg (fun j _ => sum_nonneg (fun i _ =>
    mul_nonneg (s.assignment_nonneg j i) (I.distance_nonneg j.val i.val)))

end FractionalSolution

theorem finite_additive_lp_rounding {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℕ, ∀ (I : Instance) (s : FractionalSolution I),
      ∃ S : Finset (Fin I.n), S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k+C ∧
        cost I S ≤ (1+2/Real.exp 1+ε)*(s.value:ℝ) := by
  obtain ⟨C,hC⟩ := Preparation.uniform_nonnegative_rounding hε
  refine ⟨C,?_⟩
  intro I s
  by_cases hJ : I.clients.Nonempty
  · let : Nonempty ↥I.clients := hJ.to_subtype
    let : PseudoMetricSpace (Fin I.n) := I.pseudoMetric
    obtain ⟨O,a,ha,hO,hcount,hcost⟩ := hC ↥I.facilities ↥I.clients (Fin I.n)
      s.opening s.assignment (fun j i => I.distance j.val i.val)
      Subtype.val Subtype.val s.opening_nonneg s.opening_le_one
      (fun j i => ⟨s.assignment_nonneg j i,s.assignment_le_opening j i⟩)
      s.assignment_total (fun _ _ => rfl)
    let S := O.image Subtype.val
    have hsub : S ⊆ I.facilities := by
      intro i hi
      obtain ⟨a,_,rfl⟩ := mem_image.mp hi
      exact a.property
    refine ⟨S,hsub,hO.image _,?_,?_⟩
    · have hcard : (S.card:ℝ) ≤ (O.card:ℝ) := by exact_mod_cast card_image_le
      have hbudget : (∑ i, (s.opening i:ℝ)) ≤ (I.k:ℝ) := by exact_mod_cast s.opening_budget
      have hh := hcard.trans (hcount.trans (add_le_add hbudget le_rfl))
      exact_mod_cast hh
    · have hassign := I.cost_le_assignment S (fun j => (a j).val)
        (fun j => mem_image.mpr ⟨a j,ha j,rfl⟩)
      apply hassign.trans
      have hval : (∑ j : ↥I.clients, ∑ i : ↥I.facilities,
          (s.assignment j i:ℝ)*dist (j.val) (i.val))=(s.value:ℝ) := by
        dsimp only [FractionalSolution.value]
        push_cast
        rfl
      rw [← hval]
      exact hcost
  · obtain ⟨i,hi⟩ := I.facilities_nonempty
    refine ⟨{i},singleton_subset_iff.mpr hi,singleton_nonempty _,?_,?_⟩
    · simpa only [card_singleton] using I.k_pos.trans (Nat.le_add_right I.k C)
    · have he := not_nonempty_iff_eq_empty.mp hJ
      have hz : cost I {i}=0 := by simp only [cost,he,sum_empty]
      rw [hz]
      exact mul_nonneg (by positivity) (by exact_mod_cast s.value_nonneg)

end MetricKMedian
end
end

end OAI
