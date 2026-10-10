import OAI.NumberTheory.TwoPoint.Circuits.CircuitFourierTruncation

namespace OAI

/-! Restrictions retain the coordinates in `L` and fix every other bit.
Walsh characters factor into their live and fixed coordinates. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def restrictCube {n : ℕ} (L : Finset (Fin n))
    (y x : BooleanCube n) : BooleanCube n := fun i => if i ∈ L then x i else y i

lemma walsh_restrictCube {n : ℕ} (L S : Finset (Fin n)) (y x : BooleanCube n) :
    walsh S (restrictCube L y x) = walsh (S \ L) y * walsh (S ∩ L) x := by
  have hu : S \ L ∪ S ∩ L = S := sdiff_union_inter S L
  calc
    _ = walsh (S \ L) (restrictCube L y x) *
        walsh (S ∩ L) (restrictCube L y x) := by
      simp only [walsh, ← prod_union (disjoint_sdiff_inter S L), hu]
    _ = _ := by
      congr 1
      · apply prod_congr rfl
        intro i hi
        simp only [restrictCube, ite_eq_right (mem_sdiff.mp hi).2]
      · apply prod_congr rfl
        intro i hi
        simp only [restrictCube, ite_eq_left (mem_inter.mp hi).2]

lemma WalshDegreeLE.restrict {n t : ℕ} {F : BooleanCube n → ℝ}
    (hF : WalshDegreeLE F t) (L : Finset (Fin n)) (y : BooleanCube n) :
    WalshDegreeLE (fun x => F (restrictCube L y x)) t := by
  obtain ⟨a, ha⟩ := hF
  have heq : (fun x => F (restrictCube L y x)) = fun x =>
      ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ t),
        (a S * walsh (S \ L) y) * walsh (S ∩ L) x := by
    funext x
    rw [ha]
    apply sum_congr rfl
    intro S _
    rw [walsh_restrictCube]
    ring
  rw [heq]
  apply WalshDegreeLE.sum
  intro S hS
  apply WalshDegreeLE.smul
  apply WalshDegreeLE.of_walsh
  exact (card_le_card inter_subset_left).trans (mem_filter.mp hS).2

end TwoPointCorrelations

end OAI
