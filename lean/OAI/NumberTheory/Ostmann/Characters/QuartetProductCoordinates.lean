import OAI.NumberTheory.Ostmann.Characters.QuartetMovingAction

namespace OAI

/-! # Independent held and moving coordinates on a product of quartet fibers -/

namespace Ostmann

open scoped BigOperators

noncomputable def quartetProductCoordinates {I U : Type*} [CommGroup U]
    (choice : I → QuartetMovingCase) (P : I → U) :
    ((i : I) → TreeLeafFiber U 2 (P i)) ≃ (I → U × U) × (I → U) :=
  (Equiv.piCongrRight (fun i =>
    (quartetMovingFiberEquiv (choice i) (P i)).trans (Equiv.prodAssoc U U U).symm)).trans
    (Equiv.arrowProdEquivProdArrow I (fun _ => U × U) (fun _ => U))

theorem quartetProductCoordinates_symm {I U : Type*} [CommGroup U]
    (choice : I → QuartetMovingCase) (P : I → U)
    (h : I → U × U) (r : I → U) (i : I) :
    (((quartetProductCoordinates choice P).symm (h, r)) i).1 =
      quartetMovingLeaves (choice i) (P i) (h i).1 (h i).2 (r i) := by
  exact quartetMovingFiberEquiv_symm (choice i) (P i) (h i).1 (h i).2 (r i)

theorem sum_quartetProductCoordinates {I U R : Type*} [Fintype I] [DecidableEq I] [CommGroup U]
    [Fintype U] [AddCommMonoid R] (choice : I → QuartetMovingCase) (P : I → U)
    (f : ((i : I) → TreeLeafFiber U 2 (P i)) → R) :
    (∑ m, f m) = ∑ h : I → U × U, ∑ r : I → U,
      f ((quartetProductCoordinates choice P).symm (h, r)) := by
  have h := (quartetProductCoordinates choice P).symm.bijective.sum_comp f
  simpa only [Fintype.sum_prod_type] using h.symm

theorem mean_quartetProductCoordinates {I U : Type*} [Fintype I] [DecidableEq I] [CommGroup U]
    [Fintype U] (choice : I → QuartetMovingCase) (P : I → U)
    (f : ((i : I) → TreeLeafFiber U 2 (P i)) → ℝ) :
    (Fintype.card ((i : I) → TreeLeafFiber U 2 (P i)) : ℝ)⁻¹ * (∑ m, f m) =
      ((Fintype.card (U × U) : ℝ) ^ Fintype.card I)⁻¹ *
        (∑ h : I → U × U, ((Fintype.card U : ℝ) ^ Fintype.card I)⁻¹ *
          ∑ r : I → U, f ((quartetProductCoordinates choice P).symm (h, r))) := by
  rw [sum_quartetProductCoordinates choice P,
    Fintype.card_congr (quartetProductCoordinates choice P), Fintype.card_prod]
  simp only [Fintype.card_fun, Nat.cast_mul, Nat.cast_pow, mul_inv_rev, Finset.mul_sum]
  congr 1
  ext h
  congr 1
  ext r
  ring

end Ostmann

end OAI
