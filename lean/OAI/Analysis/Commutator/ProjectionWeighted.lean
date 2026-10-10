import Mathlib
import OAI.Analysis.Commutator.ProjectionPartition

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.SpectralPartition

variable {R : Type*} [Ring R] [StarRing R] [Module ℝ R]

theorem exists_weighted_partition (n : ℕ) (p : Fin n → R) (c : Fin n → ℝ)
    (hp : ∀ i,IsStarProjection (p i)) (hc : ∀ i j,Commute (p i) (p j)) :
    ∃ (J : Type) (_ : Fintype J) (e : J → R) (d : J → ℝ),
      (∀ j,IsStarProjection (e j)) ∧
      (∀ j k,j≠k → e j*e k=0) ∧ (∑ j,e j)=1 ∧
      (∑ i,c i • p i)=∑ j,d j • e j ∧
      (∀ a : R,(∀ i,Commute a (p i)) → ∀ j,Commute a (e j)) := by
  classical
  obtain ⟨J,hJ,e,he,ho,hs,hr,ha⟩ := exists_partition n p hp hc
  let : Fintype J := hJ
  choose χ hχ using hr
  refine ⟨J,hJ,e,(fun j => ∑ i,if χ i j then c i else 0),he,ho,hs,?_,ha⟩
  calc
    (∑ i,c i • p i)=∑ i,∑ j,if χ i j then c i • e j else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hχ i,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hh : χ i j=true <;> simp [hh]
    _=∑ j,∑ i,if χ i j then c i • e j else 0 := Finset.sum_comm
    _=∑ j,(∑ i,if χ i j then c i else 0) • e j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hh : χ i j=true <;> simp [hh]

end Kadison.SpectralPartition

end

end
end

end OAI
