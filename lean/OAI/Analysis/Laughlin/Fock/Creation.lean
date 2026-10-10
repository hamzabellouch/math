import Mathlib.Algebra.Ring.Int.Units
import OAI.Analysis.Laughlin.Exterior.OccupationMetric

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupation_singleton (Q : ℕ) (i : Fin (Q+1)) :
    occupationBasis Q {i} = ExteriorAlgebra.ι ℂ (mode i) := by
  let A : Set.powersetCard (Fin (Q+1)) 1 := ⟨{i},Finset.card_singleton i⟩
  have hi : Set.powersetCard.ofFinEmbEquiv.symm A 0 = i := by
    have hm := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A
      (Set.powersetCard.ofFinEmbEquiv.symm A 0)).mp ⟨0,rfl⟩
    exact Finset.mem_singleton.mp hm
  change (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra A.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one, Function.comp_apply, hi]
  simp [Pi.basisFun_apply, mode]

theorem annihilate_unoccupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) : annihilate i (occupationBasis Q A) = 0 := by
  let d : Fin (Q+1) → ℂ := fun j => if j = i then 0 else 1
  have hd : (∏ j ∈ A, d j) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp [d, show j ≠ i by intro h; subst j; exact hi hj]
  have h := annihilate_scaling Q d i (occupationBasis Q A)
  rw [exteriorScaling_occupation,hd,one_smul] at h
  simpa [d] using h

theorem create_occupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∈ A) : create i (occupationBasis Q A) = 0 := by
  have hd : ¬Disjoint ({i} : Finset (Fin (Q+1))) A := by simpa using hi
  have h := ExteriorAlgebra.basis_mul_of_not_disjoint
    (Pi.basisFun ℂ (Fin (Q+1)))
    (⟨{i},Finset.card_singleton i⟩ : Set.powersetCard (Fin (Q+1)) 1)
    (⟨A,rfl⟩ : Set.powersetCard (Fin (Q+1)) A.card) hd
  change occupationBasis Q {i} * occupationBasis Q A = 0 at h
  rw [occupation_singleton] at h
  exact h

theorem create_unoccupied_sign (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
      create i (occupationBasis Q A) = ε • occupationBasis Q (insert i A) := by
  let S : Set.powersetCard (Fin (Q+1)) 1 := ⟨{i},Finset.card_singleton i⟩
  let T : Set.powersetCard (Fin (Q+1)) A.card := ⟨A,rfl⟩
  have hd : Disjoint S.val T.val := by simpa [S,T] using hi
  have h := ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun ℂ (Fin (Q+1))) S T hd
  rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint hd).sign with hs | hs
  · refine ⟨1,Or.inl rfl,?_⟩
    simpa [hs,S,T,occupationBasis,Set.powersetCard.disjUnion,
      ← occupation_singleton Q i, create] using h
  · refine ⟨-1,Or.inr rfl,?_⟩
    simpa [hs,S,T,occupationBasis,Set.powersetCard.disjUnion,
      ← occupation_singleton Q i, create] using h

end Laughlin.Fock

end OAI
