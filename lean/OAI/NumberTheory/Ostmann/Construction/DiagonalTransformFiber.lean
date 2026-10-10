import OAI.NumberTheory.Ostmann.Construction.DiagonalRegrouping
import OAI.NumberTheory.Ostmann.Construction.DiagonalTransformBasic

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

def diagonalCoefficientTerm (z : RemainingTerm sources seed V giant l) : ℂ :=
  actualCoefficient sources seed V X G (residueTransform d) bins outside l
    (remainingState sources (Template.current seed l) (l+1) giant p u z.1 z.2.val)

def diagonalHalfTransform (z : RemainingTerm sources seed V giant l) : ℂ :=
  halfTransform (residueTransform d) (favorableGiantResidueTransform d P)
    (outsideProduct outside*halfProduct p
      (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u))
    z.2.val z.1.1.val
    (assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) z.1.2)

lemma remainingTermValue_eq_diagonalHalfTransform_mul (z : RemainingTerm sources seed V giant l) :
    remainingTermValue d P sources seed V giant X G bins outside l p u z=
      diagonalHalfTransform d P sources seed V giant outside l p u z*
        diagonalCoefficientTerm d sources seed V giant X G bins outside l p u z := rfl

theorem diagonalHalfTransform_eq_of_tag (x y : RemainingTerm sources seed V giant l)
    (hx : remainingTermMass sources seed V giant l x≠0)
    (hy : remainingTermMass sources seed V giant l y≠0)
    (hsep : ∀i:Fin (Template.remainder (l+1) (Template.current seed l)).length,
      giant.DisjointMass (sources (Template.remainder (l+1) (Template.current seed l))[i].origin))
    (htag : remainingTermProductTag sources seed V giant l x=
      remainingTermProductTag sources seed V giant l y) :
    diagonalHalfTransform d P sources seed V giant outside l p u x=
      diagonalHalfTransform d P sources seed V giant outside l p u y := by
  have hv : x.2.val=y.2.val := congrArg Prod.fst htag
  have hH : remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant x.1=
      remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant y.1 :=
    congrArg Prod.snd htag
  unfold diagonalHalfTransform
  rw [hv]
  exact remaining_halfTransform_eq_of_mass_product sources _ giant x.1 y.1 hx hy hsep hH _ _ _ _

theorem diagonal_grouped_transform_factor
    (hsep : ∀i:Fin (Template.remainder (l+1) (Template.current seed l)).length,
      giant.DisjointMass (sources (Template.remainder (l+1) (Template.current seed l))[i].origin))
    (z₀ : RemainingTerm sources seed V giant l)
    (hz₀ : remainingTermMass sources seed V giant l z₀≠0) :
    groupedValue Finset.univ (remainingTermProductTag sources seed V giant l)
      (fun z => (remainingTermMass sources seed V giant l z:ℂ)*
        remainingTermValue d P sources seed V giant X G bins outside l p u z)
      (remainingTermProductTag sources seed V giant l z₀) =
    diagonalHalfTransform d P sources seed V giant outside l p u z₀ *
      groupedValue Finset.univ (remainingTermProductTag sources seed V giant l)
        (fun z => (remainingTermMass sources seed V giant l z:ℂ)*
          diagonalCoefficientTerm d sources seed V giant X G bins outside l p u z)
        (remainingTermProductTag sources seed V giant l z₀) := by
  unfold groupedValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  dsimp only
  by_cases hm : remainingTermMass sources seed V giant l z=0
  · simp only [hm,Complex.ofReal_zero,zero_mul,mul_zero]
  · rw [remainingTermValue_eq_diagonalHalfTransform_mul,
      diagonalHalfTransform_eq_of_tag d P sources seed V giant outside l p u z z₀ hm hz₀ hsep
        (Finset.mem_filter.mp hz).2]
    ring

theorem diagonal_grouped_square_le_smallMultiplier
    (hsep : ∀i:Fin (Template.remainder (l+1) (Template.current seed l)).length,
      giant.DisjointMass (sources (Template.remainder (l+1) (Template.current seed l))[i].origin))
    (z₀ : RemainingTerm sources seed V giant l)
    (hz₀ : remainingTermMass sources seed V giant l z₀≠0) :
    ‖groupedValue Finset.univ (remainingTermProductTag sources seed V giant l)
      (fun z => (remainingTermMass sources seed V giant l z:ℂ)*
        remainingTermValue d P sources seed V giant X G bins outside l p u z)
      (remainingTermProductTag sources seed V giant l z₀)‖^2 ≤
    diagonalSmallMultiplier d
      (outsideProduct outside*halfProduct p
        (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u))
      z₀.2.val z₀.1.1.val
      (assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) z₀.1.2) *
      ‖groupedValue Finset.univ (remainingTermProductTag sources seed V giant l)
        (fun z => (remainingTermMass sources seed V giant l z:ℂ)*
          diagonalCoefficientTerm d sources seed V giant X G bins outside l p u z)
        (remainingTermProductTag sources seed V giant l z₀)‖^2 := by
  rw [diagonal_grouped_transform_factor d P sources seed V giant X G bins outside l p u hsep z₀ hz₀,
    norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (halfTransform_norm_sq_le_smallMultiplier d P _ _ _ _)
    (sq_nonneg _)

end
end Ostmann.Construction

end

end OAI
