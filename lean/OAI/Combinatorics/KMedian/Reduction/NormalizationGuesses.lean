import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalInstanceCost

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Instance

theorem rationalNearest_nonneg (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) :
    0 ≤ rationalNearest I j S := by
  have hh := I.nearest_nonneg j S
  rw [← I.cast_rationalNearest] at hh
  exact_mod_cast hh

theorem rationalNearest_attained (I : Instance) (j : Fin I.n)
    (S : Finset (Fin I.n)) (hS : S.Nonempty) :
    ∃ i ∈ S, rationalNearest I j S=I.distance j i := by
  unfold rationalNearest
  rw [dite_eq_left hS]
  obtain ⟨i,hi,he⟩ := mem_image.mp (min'_mem (S.image (I.distance j)) (hS.image _))
  exact ⟨i,hi,he.symm⟩

theorem maximum_connection (I : Instance) (S : Finset (Fin I.n)) (hS : S.Nonempty)
    (hc : 0 < rationalCost I S) :
    ∃ j ∈ I.clients, ∃ i ∈ S,
      0 < I.distance j i ∧ I.distance j i ≤ rationalCost I S ∧
        rationalCost I S ≤ (I.n:ℚ)*I.distance j i := by
  have hJ : I.clients.Nonempty := by
    by_contra h
    have he := not_nonempty_iff_eq_empty.mp h
    simp only [rationalCost,he,sum_empty] at hc
    exact lt_irrefl 0 hc
  let A := I.clients.image (fun j => rationalNearest I j S)
  have hA : A.Nonempty := hJ.image _
  obtain ⟨j,hj,he⟩ := mem_image.mp (max'_mem A hA)
  obtain ⟨i,hi,hd⟩ := I.rationalNearest_attained j S hS
  have hmax : ∀ a ∈ I.clients, rationalNearest I a S ≤ I.distance j i := by
    intro a ha
    rw [← hd,he]
    exact le_max' A _ (mem_image_of_mem _ ha)
  have hupper : rationalCost I S ≤ (I.n:ℚ)*I.distance j i := by
    calc
      _ ≤ ∑ _a ∈ I.clients, I.distance j i := sum_le_sum hmax
      _ = (I.clients.card:ℚ)*I.distance j i := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show I.clients.card ≤ I.n by simpa using card_le_univ I.clients))
        (I.distance_nonneg j i)
  have hpos : 0 < I.distance j i := by
    by_contra h
    have hz : I.distance j i=0 := le_antisymm (le_of_not_gt h) (I.distance_nonneg j i)
    rw [hz,mul_zero] at hupper
    exact (not_lt_of_ge hupper) hc
  refine ⟨j,hj,i,hi,hpos,?_,hupper⟩
  rw [← hd]
  exact single_le_sum (fun a _ => I.rationalNearest_nonneg a S) hj

end Instance

namespace Normalization

theorem dyadic_bracket (c d : ℚ) (N : ℕ) (hd : 0 < d) (hc : d ≤ c)
    (hupper : c ≤ d*(2:ℚ)^N) :
    ∃ t ≤ N, c ≤ d*(2:ℚ)^t ∧ d*(2:ℚ)^t ≤ 2*c := by
  induction N with
  | zero =>
    refine ⟨0,le_rfl,hupper,?_⟩
    simp only [pow_zero,mul_one]
    linarith
  | succ N ih =>
    by_cases h : c ≤ d*(2:ℚ)^N
    · obtain ⟨t,ht,h1,h2⟩ := ih h
      exact ⟨t,by omega,h1,h2⟩
    · refine ⟨N+1,le_rfl,hupper,?_⟩
      rw [pow_succ]
      have hh := lt_of_not_ge h
      nlinarith

def guesses (I : Instance) : Finset ℚ :=
  (univ : Finset (Fin I.n × Fin I.n)).biUnion (fun a =>
    if 0 < I.distance a.1 a.2 then
      (range (I.n.size+1)).image (fun t => I.distance a.1 a.2*(2:ℚ)^t)
    else ∅)

theorem guesses_pos (I : Instance) (B : ℚ) (hB : B ∈ guesses I) : 0 < B := by
  obtain ⟨a,_,ha⟩ := mem_biUnion.mp hB
  split_ifs at ha with h
  · obtain ⟨t,_,rfl⟩ := mem_image.mp ha
    exact mul_pos h (by positivity)
  · exact False.elim (notMem_empty _ ha)

theorem guesses_card (I : Instance) : (guesses I).card ≤ I.n*I.n*(I.n.size+1) := by
  calc
    _ ≤ ∑ a : Fin I.n × Fin I.n,
        (if 0 < I.distance a.1 a.2 then
          (range (I.n.size+1)).image (fun t => I.distance a.1 a.2*(2:ℚ)^t)
          else ∅).card := card_biUnion_le
    _ ≤ ∑ _a : Fin I.n × Fin I.n, (I.n.size+1) := by
      apply sum_le_sum
      intro a _
      split_ifs
      · exact card_image_le.trans (card_range _).le
      · simp only [card_empty]; omega
    _ = _ := by simp

theorem good_guess (I : Instance) (S : Finset (Fin I.n)) (hS : S.Nonempty)
    (hc : 0 < rationalCost I S) :
    ∃ B ∈ guesses I, 0 < B ∧
      1/2 ≤ rationalCost I S/B ∧ rationalCost I S/B ≤ 1 := by
  obtain ⟨j,_,i,_,hd,hl,hu⟩ := I.maximum_connection S hS hc
  have hn : (I.n:ℚ) ≤ (2:ℚ)^I.n.size := by
    exact_mod_cast ((Nat.size_le).mp (le_refl I.n.size)).le
  have hcupper : rationalCost I S ≤ I.distance j i*(2:ℚ)^I.n.size :=
    hu.trans (by nlinarith only [mul_le_mul_of_nonneg_right hn hd.le])
  obtain ⟨t,ht,h1,h2⟩ := dyadic_bracket _ _ I.n.size hd hl hcupper
  let B := I.distance j i*(2:ℚ)^t
  have hB : 0 < B := mul_pos hd (by positivity)
  refine ⟨B,mem_biUnion.mpr ⟨(j,i),mem_univ _,?_⟩,hB,?_,?_⟩
  · simp only [ite_eq_left hd]
    exact mem_image.mpr ⟨t,mem_range.mpr (by omega),rfl⟩
  · apply (le_div_iff₀ hB).mpr
    change 1/2*B ≤ _
    change B ≤ 2*rationalCost I S at h2
    linarith
  · exact (div_le_one hB).mpr h1

end Normalization
end MetricKMedian
end
end

end OAI
