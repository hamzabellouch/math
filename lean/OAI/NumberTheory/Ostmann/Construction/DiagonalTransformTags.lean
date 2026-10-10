import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexSupport
import OAI.NumberTheory.Ostmann.Construction.DiagonalTransformFiber

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def diagonalMassTags (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (giant : PrimeSource) (l : ℕ) : Finset (ℤ×ℕ) := by
  classical
  exact (Finset.univ.filter (fun z : RemainingTerm sources seed V giant l =>
    remainingTermMass sources seed V giant l z≠0)).image
      (remainingTermProductTag sources seed V giant l)

def diagonalMassRepresentative (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (giant : PrimeSource) (l : ℕ) (t : ↥(diagonalMassTags sources seed V giant l)) :
    RemainingTerm sources seed V giant l :=
  Classical.choose (Finset.mem_image.mp t.property)

theorem diagonalMassRepresentative_spec (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (giant : PrimeSource) (l : ℕ) (t : ↥(diagonalMassTags sources seed V giant l)) :
    remainingTermMass sources seed V giant l (diagonalMassRepresentative sources seed V giant l t)≠0 ∧
    remainingTermProductTag sources seed V giant l (diagonalMassRepresentative sources seed V giant l t)=t.val := by
  classical
  have hs := Classical.choose_spec (Finset.mem_image.mp t.property)
  exact ⟨(Finset.mem_filter.mp hs.1).2,hs.2⟩

theorem remainingDiagonal_eq_massTag_grouped_squares (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource)
    (X G : ℝ) (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (hg : giant.AboveFrequency (V l))
    (hs : ∀i:Fin (Template.remainder (l+1) (Template.current seed l)).length,
      (sources (Template.remainder (l+1) (Template.current seed l))[i].origin).AboveFrequency (V l)) :
    remainingDiagonal d P sources seed V giant X G bins outside l p u =
      ∑t:↥(diagonalMassTags sources seed V giant l),
        ‖groupedValue Finset.univ (remainingTermProductTag sources seed V giant l)
          (fun z => (remainingTermMass sources seed V giant l z:ℂ)*
            remainingTermValue d P sources seed V giant X G bins outside l p u z) t.val‖^2 := by
  classical
  let tag := remainingTermProductTag sources seed V giant l
  let f := fun z => (remainingTermMass sources seed V giant l z:ℂ)*
    remainingTermValue d P sources seed V giant X G bins outside l p u z
  have he : remainingDiagonal d P sources seed V giant X G bins outside l p u =
      ∑t∈Finset.univ.image tag,‖groupedValue Finset.univ tag f t‖^2 := by
    rw [remainingDiagonal_eq_product_diagonal_of_positive_mass d P sources seed V giant X G bins outside l p u hg hs]
    unfold refinedRowDiagonal
    rw [diagonal_eq_grouped_squares]
    simp only [Complex.ofReal_re]
    rfl
  have hsub : diagonalMassTags sources seed V giant l ⊆ Finset.univ.image tag := by
    intro t ht
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_image_of_mem tag (Finset.mem_univ z)
  have hrestrict : (∑t∈diagonalMassTags sources seed V giant l,‖groupedValue Finset.univ tag f t‖^2)=
      ∑t∈Finset.univ.image tag,‖groupedValue Finset.univ tag f t‖^2 := by
    apply Finset.sum_subset hsub
    intro t ht hnot
    have hz : groupedValue Finset.univ tag f t=0 := by
      apply Finset.sum_eq_zero
      intro z hz
      have hm : remainingTermMass sources seed V giant l z=0 := by
        by_contra hm
        apply hnot
        exact Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ z,hm⟩,
          (Finset.mem_filter.mp hz).2⟩
      simp only [f,hm,Complex.ofReal_zero,zero_mul]
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]
  calc
    _ = ∑t∈Finset.univ.image tag,‖groupedValue Finset.univ tag f t‖^2 := he
    _ = ∑t∈diagonalMassTags sources seed V giant l,‖groupedValue Finset.univ tag f t‖^2 := hrestrict.symm
    _ = _ := (Finset.sum_coe_sort _ _).symm

end Ostmann.Construction

end

end OAI
