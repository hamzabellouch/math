import OAI.NumberTheory.Ostmann.Construction.DiagonalTransformBasic
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

theorem diagonalSmallMultiplier_eq_of_value_perm (d : Decomposition) (D : ℕ)
    (v : ℤ) (q : ℕ) (xs ys : List SmallSlot)
    (hperm : (xs.map SmallSlot.value).Perm (ys.map SmallSlot.value)) :
    diagonalSmallMultiplier d D v q xs=diagonalSmallMultiplier d D v q ys := by
  have hH : halfProduct q xs=halfProduct q ys := congrArg (fun n => q*n) hperm.prod_eq
  unfold diagonalSmallMultiplier
  rw [hH]
  simpa only [List.map_map,Function.comp_def] using
    (hperm.map (fun p : ℕ => ‖residueTransform d p
      (modFraction p v (D*(halfProduct q ys/p)))‖^2)).prod_eq

theorem remaining_smallMultiplier_eq_of_mass_product
    (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x y : RemainingSample sources T giant)
    (hx : (remainingPrior sources T giant).mass x≠0)
    (hy : (remainingPrior sources T giant).mass y≠0)
    (hsep : ∀i:Fin T.length,giant.DisjointMass (sources T[i].origin))
    (he : remainingProduct sources T giant x=remainingProduct sources T giant y)
    (d : Decomposition) (D : ℕ) (v : ℤ) :
    diagonalSmallMultiplier d D v x.1.val (assignedSlots sources T x.2)=
      diagonalSmallMultiplier d D v y.1.val (assignedSlots sources T y.2) := by
  have hg := remaining_giant_eq_of_product_eq_of_mass sources T giant x y hx hy hsep he
  have hp := remainingValues_perm_of_product_eq sources T giant x y he
  change (x.1.val::_).Perm (y.1.val::_) at hp
  rw [hg] at hp ⊢
  exact diagonalSmallMultiplier_eq_of_value_perm d D v y.1.val _ _ (List.Perm.cons_inv hp)

namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem giant_sources_disjointMass (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (hsep : C.CrossRoleSeparation spectator) (origin : ℕ) :
    C.giant.DisjointMass (C.sources origin) := by
  unfold sources NominalCenterArray.sources initialSourceFamily initialSourceValue
  split_ifs
  · exact hsep.bulk_giant.symm
  · exact hsep.giant_aux (.inl _)
  · exact hsep.giant_aux (.inr (_,_))
  · exact hsep.bulk_giant.symm

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
