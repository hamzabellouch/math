import OAI.Analysis.Laughlin.Charge.Sectors

namespace OAI

namespace Laughlin.Charge
open Fock
open scoped BigOperators

theorem vacuum_fockDegree (Q : ℕ) : FockDegree Q 0 (1 : Space Q) := by
  intro A hA
  have hne : (∅ : Finset (Fin (Q+1)))≠A := by
    intro he
    subst A
    simp at hA
  rw [← occupation_empty]
  simp [Module.Basis.repr_self,hne]

theorem orderedWedge_fockDegree (n Q : ℕ) (a : Configuration n Q) :
    FockDegree Q (n : ℤ) (orderedWedge a) := by
  induction n with
  | zero =>
    simpa only [Nat.cast_zero,orderedWedge,ExteriorAlgebra.ιMulti_zero_apply] using vacuum_fockDegree Q
  | succ n ih =>
    rw [orderedWedge_head]
    simpa only [Nat.cast_add,Nat.cast_one] using
      fockDegree_create (ih (fun j => a j.succ)) (a 0)

theorem tensorExterior_fockDegree (n Q : ℕ) (ψ : State n Q) :
    FockDegree Q (n : ℤ) (tensorExterior n Q ψ) := by
  change FockDegree Q (n : ℤ) (∑ a, ψ a • orderedWedge a)
  apply fockDegree_sum
  intro a ha
  exact fockDegree_smul (orderedWedge_fockDegree n Q a) (ψ a)

theorem normalizedTensorExterior_fockDegree (n Q : ℕ) (ψ : State n Q) :
    FockDegree Q (n : ℤ) (normalizedTensorExterior n Q ψ) :=
  fockDegree_smul (tensorExterior_fockDegree n Q ψ) _

theorem occupationBasis_eq_orderedWedge (n Q : ℕ) (A : Finset (Fin (Q+1)))
    (hA : A.card=n) :
    occupationBasis Q A = orderedWedge
      (Set.powersetCard.ofFinEmbEquiv.symm (⟨A,hA⟩ : Set.powersetCard (Fin (Q+1)) n)) := by
  let S : Set.powersetCard (Fin (Q+1)) n := ⟨A,hA⟩
  change (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra S.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family,orderedWedge,mode]
  congr 1
  funext i
  simp only [Function.comp_apply,Pi.basisFun_apply]
  rfl

theorem occupationInner_basis_coefficient (Q : ℕ) (A : Finset (Fin (Q+1))) (x : Space Q) :
    occupationInner Q (occupationBasis Q A) x=(occupationBasis Q).repr x A := by
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem normalizedTensorReadout_injective_sector (n Q : ℕ) (x y : Space Q)
    (hx : FockDegree Q (n : ℤ) x) (hy : FockDegree Q (n : ℤ) y)
    (he : normalizedTensorReadout n Q x=normalizedTensorReadout n Q y) : x=y := by
  apply (occupationBasis Q).repr.injective
  ext A
  by_cases hA : A.card=n
  · let a : Configuration n Q :=
      Set.powersetCard.ofFinEmbEquiv.symm (⟨A,hA⟩ : Set.powersetCard (Fin (Q+1)) n)
    have h := congrFun he a
    change ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ)*occupationInner Q (orderedWedge a) x=
      ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ)*occupationInner Q (orderedWedge a) y at h
    have hs : ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ)≠0 := by
      exact_mod_cast (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr
        (show (0 : ℝ)<n.factorial by exact_mod_cast Nat.factorial_pos n))))
    have hh := mul_left_cancel₀ hs h
    have hw : orderedWedge a=occupationBasis Q A :=
      (occupationBasis_eq_orderedWedge n Q A hA).symm
    rw [hw,occupationInner_basis_coefficient,occupationInner_basis_coefficient] at hh
    exact hh
  · rw [hx A (by exact_mod_cast hA),hy A (by exact_mod_cast hA)]

theorem normalizedTensorExterior_readout (n Q : ℕ) (x : Space Q)
    (hx : FockDegree Q (n : ℤ) x) :
    normalizedTensorExterior n Q (normalizedTensorReadout n Q x)=x := by
  apply normalizedTensorReadout_injective_sector n Q _ x
    (normalizedTensorExterior_fockDegree n Q _) hx
  exact normalizedTensorReadout_left_inverse n Q _ (normalizedTensorReadout_antisymmetric n Q x)

end Laughlin.Charge

end OAI
