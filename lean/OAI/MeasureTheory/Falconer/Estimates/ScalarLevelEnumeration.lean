import OAI.MeasureTheory.Falconer.Estimates.ScalarNonporousDoubling
import Mathlib.Data.Finset.Sort

namespace OAI

/-! Enumerating selected scalar blocks in geometric order, with a final
 sentinel for the gap after the last selected block. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_level_enumeration (M : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range M) :
    ∃ g : ℕ → ℕ, (∀ i < S.card, g i ∈ S) ∧
      (∀ i < S.card, g i < g (i+1)) ∧ (∀ i < S.card, g i < M) := by
  classical
  let E := S.orderIsoOfFin rfl
  let g := fun i : ℕ => if hi : i < S.card then (E ⟨i,hi⟩).val else M
  have hm : ∀ i < S.card, g i ∈ S := by
    intro i hi
    simpa only [g,dite_eq_left hi] using (E ⟨i,hi⟩).property
  have hb : ∀ i < S.card, g i < M := fun i hi => Finset.mem_range.mp (hS (hm i hi))
  refine ⟨g,hm,?_,hb⟩
  intro i hi
  by_cases hj : i+1 < S.card
  · have he : (E ⟨i,hi⟩).val < (E ⟨i+1,hj⟩).val := E.strictMono (by simp)
    simpa only [g,dite_eq_left hi,dite_eq_left hj] using he
  · simpa only [g,dite_eq_left hi,dite_eq_right hj] using hb i hi

noncomputable def scalarNonporousLevels (M B C : ℕ) (branch n : ℕ → ℕ) : Finset ℕ :=
  (Finset.range M).filter fun i => branch i ≠ 0 ∧ B*(i+1) ≤ n i+C

 theorem scalar_nonporous_levels_bound {B M copies J L C : ℕ} {U K : ℝ}
    (Q : Finset (CellPath 1)) (hQ : Q ⊆ cubePaths 1 (B*M)) (hne : Q.Nonempty)
    (branch n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (B*i) (B*(i+1)) (branch i) (n i))
    (hU : 18*(2:ℝ)^C ≤ U) (hJ : 0 < J)
    (hcontract : (1/2:ℝ)^B*(1+2*(J:ℝ)*U) ≤ 1)
    (hL : 4*(J:ℝ)*U ≤ (L:ℝ)) (hcopies : (2*L+1)*J ≤ copies)
    (hK : 0 ≤ K)
    (hsmall : ((scalarCells ((1/2:ℝ)^(B*M))
      (Q.image scalarPathCenter+Q.image scalarPathCenter)).card:ℝ) ≤
      K*(scalarCells ((1/2:ℝ)^(B*M)) (Q.image scalarPathCenter)).card) :
    (((J+1)^(scalarNonporousLevels M B C branch n).card:ℕ):ℝ) ≤
      (copies+2)*(2*K)^copies*(Q.card:ℝ) := by
  let S := scalarNonporousLevels M B C branch n
  obtain ⟨g,hm,hg,hb⟩ := scalar_level_enumeration M S (Finset.filter_subset _ _)
  apply scalar_nonporous_doubling_bound Q hQ hne branch n hlevel S.card g hg hb
    (fun i hi => (Finset.mem_filter.mp (hm i hi)).2.1)
    (fun i hi => (Finset.mem_filter.mp (hm i hi)).2.2) hU hJ hcontract hL hcopies hK hsmall

end Falconer.Regularization

end OAI
