import OAI.NumberTheory.Ostmann.Construction.DiagonalTransformSmall
import OAI.NumberTheory.Ostmann.Construction.DiagonalTransformTags

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
section
variable (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))

def diagonalSmallTerm (z : RemainingTerm sources seed V giant l) : ℝ :=
  diagonalSmallMultiplier d
    (outsideProduct outside*halfProduct p
      (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u))
    z.2.val z.1.1.val
    (assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) z.1.2)

theorem remainingDiagonal_eq_transform_groups
    (hg : giant.AboveFrequency (V l))
    (hs : ∀i:Fin (Template.remainder (l+1) (Template.current seed l)).length,
      (sources (Template.remainder (l+1) (Template.current seed l))[i].origin).AboveFrequency (V l))
    (hsep : ∀i:Fin (Template.remainder (l+1) (Template.current seed l)).length,
      giant.DisjointMass (sources (Template.remainder (l+1) (Template.current seed l))[i].origin)) :
    remainingDiagonal d P sources seed V giant X G bins outside l p u =
      ∑t:↥(diagonalMassTags sources seed V giant l),
        ‖diagonalHalfTransform d P sources seed V giant outside l p u
          (diagonalMassRepresentative sources seed V giant l t)‖^2 *
        ‖groupedValue Finset.univ (remainingTermProductTag sources seed V giant l)
          (fun z => (remainingTermMass sources seed V giant l z:ℂ)*
            diagonalCoefficientTerm d sources seed V giant X G bins outside l p u z) t.val‖^2 := by
  rw [remainingDiagonal_eq_massTag_grouped_squares d P sources seed V giant X G bins outside l p u hg hs]
  apply Finset.sum_congr rfl
  intro t ht
  have hr := diagonalMassRepresentative_spec sources seed V giant l t
  have he := diagonal_grouped_transform_factor d P sources seed V giant X G bins outside l p u
    hsep (diagonalMassRepresentative sources seed V giant l t) hr.1
  rw [hr.2] at he
  rw [he,norm_mul,mul_pow]

theorem remainingDiagonal_le_small_transform_groups
    (hg : giant.AboveFrequency (V l))
    (hs : ∀i:Fin (Template.remainder (l+1) (Template.current seed l)).length,
      (sources (Template.remainder (l+1) (Template.current seed l))[i].origin).AboveFrequency (V l))
    (hsep : ∀i:Fin (Template.remainder (l+1) (Template.current seed l)).length,
      giant.DisjointMass (sources (Template.remainder (l+1) (Template.current seed l))[i].origin)) :
    remainingDiagonal d P sources seed V giant X G bins outside l p u ≤
      ∑t:↥(diagonalMassTags sources seed V giant l),
        diagonalSmallTerm d sources seed V giant outside l p u
          (diagonalMassRepresentative sources seed V giant l t) *
        ‖groupedValue Finset.univ (remainingTermProductTag sources seed V giant l)
          (fun z => (remainingTermMass sources seed V giant l z:ℂ)*
            diagonalCoefficientTerm d sources seed V giant X G bins outside l p u z) t.val‖^2 := by
  rw [remainingDiagonal_eq_transform_groups d P sources seed V giant X G bins outside l p u hg hs hsep]
  apply Finset.sum_le_sum
  intro t ht
  exact mul_le_mul_of_nonneg_right (halfTransform_norm_sq_le_smallMultiplier d P _ _ _ _)
    (sq_nonneg _)

theorem diagonalSmallTerm_eq_of_tag (x y : RemainingTerm sources seed V giant l)
    (hx : remainingTermMass sources seed V giant l x≠0)
    (hy : remainingTermMass sources seed V giant l y≠0)
    (hsep : ∀i:Fin (Template.remainder (l+1) (Template.current seed l)).length,
      giant.DisjointMass (sources (Template.remainder (l+1) (Template.current seed l))[i].origin))
    (htag : remainingTermProductTag sources seed V giant l x=
      remainingTermProductTag sources seed V giant l y) :
    diagonalSmallTerm d sources seed V giant outside l p u x=
      diagonalSmallTerm d sources seed V giant outside l p u y := by
  have hv : x.2.val=y.2.val := congrArg Prod.fst htag
  have hH : remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant x.1=
      remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant y.1 :=
    congrArg Prod.snd htag
  unfold diagonalSmallTerm
  rw [hv]
  exact remaining_smallMultiplier_eq_of_mass_product sources _ giant x.1 y.1 hx hy hsep hH _ _ _

end
end Ostmann.Construction

end

end OAI
