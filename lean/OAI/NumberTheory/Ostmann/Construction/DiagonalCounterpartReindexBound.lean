import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexExpansion

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Ostmann.Construction
section
variable (d : Decomposition) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ) (bins : List ℕ→State→ℝ)
    (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))

def smallTransformGroupedBound : ℝ :=
  ∑t : ↥(diagonalMassTags sources seed V giant l),
    diagonalSmallTerm d sources seed V giant outside l p u
      (diagonalMassRepresentative sources seed V giant l t)*
    ‖groupedValue Finset.univ (remainingTermProductTag sources seed V giant l)
      (fun z => (remainingTermMass sources seed V giant l z:ℂ)*
        diagonalCoefficientTerm d sources seed V giant X G bins outside l p u z) t.val‖^2

def smallTransformCoefficientPairing : ℝ :=
  (∑z : RemainingTerm sources seed V giant l,
    (diagonalSmallTerm d sources seed V giant outside l p u z:ℂ)*
    ((remainingTermMass sources seed V giant l z:ℂ)*
      diagonalCoefficientTerm d sources seed V giant X G bins outside l p u z)*
    conj (groupedValue Finset.univ (remainingTermProductTag sources seed V giant l)
      (fun y => (remainingTermMass sources seed V giant l y:ℂ)*
        diagonalCoefficientTerm d sources seed V giant X G bins outside l p u y)
      (remainingTermProductTag sources seed V giant l z))).re

def smallTransformCounterpartPairing : ℝ :=
  (∑x : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant,
    ∑v : AllowedFrequency V l,
      ((remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass x:ℂ)*
      (diagonalSmallTerm d sources seed V giant outside l p u (x,v):ℂ)*
      diagonalCoefficientTerm d sources seed V giant X G bins outside l p u (x,v)*
      conj (bandCounterpartSum sources (Template.remainder (l+1) (Template.current seed l)) giant x
        (fun y => diagonalCoefficientTerm d sources seed V giant X G bins outside l p u (y,v)))).re

theorem smallTransformGroupedBound_eq_coefficientPairing
    (hsep : ∀i : Fin (Template.remainder (l+1) (Template.current seed l)).length,
      giant.DisjointMass (sources (Template.remainder (l+1) (Template.current seed l))[i].origin)) :
    smallTransformGroupedBound d sources seed V giant X G bins outside l p u=
      smallTransformCoefficientPairing d sources seed V giant X G bins outside l p u := by
  let tag := remainingTermProductTag sources seed V giant l
  let F : RemainingTerm sources seed V giant l→ℂ := fun z =>
    (remainingTermMass sources seed V giant l z:ℂ)*
      diagonalCoefficientTerm d sources seed V giant X G bins outside l p u z
  let M := diagonalSmallTerm d sources seed V giant outside l p u
  have hcover : ∀z,F z≠0→tag z∈diagonalMassTags sources seed V giant l := by
    intro z hz
    have hm : remainingTermMass sources seed V giant l z≠0 := by
      have hm := (mul_ne_zero_iff.mp hz).1
      exact_mod_cast hm
    exact Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ z,hm⟩,rfl⟩
  have hM : ∀t : ↥(diagonalMassTags sources seed V giant l),∀z,
      tag z=t.val→F z≠0→M z=M (diagonalMassRepresentative sources seed V giant l t) := by
    intro t z hz hF
    have hm : remainingTermMass sources seed V giant l z≠0 := by
      have hm := (mul_ne_zero_iff.mp hF).1
      exact_mod_cast hm
    have hr := diagonalMassRepresentative_spec sources seed V giant l t
    exact diagonalSmallTerm_eq_of_tag d sources seed V giant outside l p u z _ hm hr.1 hsep
      (hz.trans hr.2.symm)
  have he := grouped_multiplier_expansion tag F M (diagonalMassTags sources seed V giant l)
    (diagonalMassRepresentative sources seed V giant l) hcover hM
  exact (Complex.ofReal_re _).symm.trans (congrArg Complex.re he)

theorem smallTransformCoefficientPairing_eq_counterpartPairing
    (hsep : RemainingBandsSeparated sources (Template.remainder (l+1) (Template.current seed l)) giant) :
    smallTransformCoefficientPairing d sources seed V giant X G bins outside l p u=
      smallTransformCounterpartPairing d sources seed V giant X G bins outside l p u := by
  unfold smallTransformCoefficientPairing smallTransformCounterpartPairing
  apply congrArg Complex.re
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hmx : (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass x=0
  · simp only [remainingTermMass,hmx,Complex.ofReal_zero,zero_mul,mul_zero]
  by_cases hA : diagonalCoefficientTerm d sources seed V giant X G bins outside l p u (x,v)=0
  · simp only [hA,mul_zero,zero_mul]
  rw [diagonal_grouped_coefficient_eq_band_counterpart d sources seed V giant X G bins outside l p u x v hsep hmx hA]
  have halg (a b c e : ℂ) : a*(b*c)*e=b*a*c*e := by ring
  exact halg _ _ _ _

theorem remainingDiagonal_le_small_counterpart_pairing (P : Finset ℕ)
    (hg : giant.AboveFrequency (V l))
    (hs : ∀i : Fin (Template.remainder (l+1) (Template.current seed l)).length,
      (sources (Template.remainder (l+1) (Template.current seed l))[i].origin).AboveFrequency (V l))
    (hsep : RemainingBandsSeparated sources (Template.remainder (l+1) (Template.current seed l)) giant) :
    remainingDiagonal d P sources seed V giant X G bins outside l p u ≤
      smallTransformCounterpartPairing d sources seed V giant X G bins outside l p u := by
  have hgsep : ∀i : Fin (Template.remainder (l+1) (Template.current seed l)).length,
      giant.DisjointMass (sources (Template.remainder (l+1) (Template.current seed l))[i].origin) := by
    intro i
    exact hsep 0 i.succ (by simp [remainingPositionBand])
  have hb := remainingDiagonal_le_small_transform_groups d P sources seed V giant X G bins outside l p u hg hs hgsep
  change remainingDiagonal d P sources seed V giant X G bins outside l p u ≤
    smallTransformGroupedBound d sources seed V giant X G bins outside l p u at hb
  rwa [smallTransformGroupedBound_eq_coefficientPairing d sources seed V giant X G bins outside l p u hgsep,
    smallTransformCoefficientPairing_eq_counterpartPairing d sources seed V giant X G bins outside l p u hsep] at hb

end
end Ostmann.Construction

end

end OAI
