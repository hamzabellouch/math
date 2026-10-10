import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.SymbolDetection
import OAI.Combinatorics.Chromatic.Shuffle.VariableMean

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.CenterCalculus
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma proper_next_iff_symbols_zero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)
    (f : sourceFiltration a c η hc θ d W) :
    f.val∈properSourceFiltration a c η hc θ d (W+1) ↔
      ∀ j : SymbolIndex c η θ d,j.tree.IsProper → symbolFamily a c η hc θ hχ d W f j=0 := by
  constructor
  · intro hf j hp
    obtain ⟨T,ho,hs,hd⟩:=j
    subst d
    change SplitTree.normalizedSymbol a c η hc θ T hs _ W f=0
    rw [SplitTree.normalizedSymbol_eq_zero_iff]
    ext z
    simp only [SplitTree.totalLeadingPolynomial,coeff_mapLinear,
      AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
    apply SplitTree.componentTensor_detect a (SlopeArithmetic.slope c η) T
    intro k
    rw [SplitTree.componentTensor_weightComponent]
    split_ifs with hw
    · exact hf T ho hp hs rfl k z (by omega)
    · rfl
  · intro hf
    rw [proper_next_iff_leading_zero]
    intro j hp
    obtain ⟨T,ho,hs,hd,k,z,hw⟩:=j
    have hh:=hf ⟨T,ho,hs,hd⟩ hp
    subst d
    change SplitTree.normalizedSymbol a c η hc θ T hs _ W f=0 at hh
    rw [SplitTree.normalizedSymbol_eq_zero_iff] at hh
    exact SplitTree.totalLeadingPolynomial_zero_test a c η hc θ T hs W f.val hh k z hw

noncomputable def primitiveSpace (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ) :
    Submodule ℚ (SourceAssociatedGrade a c η hc θ d W) :=
  LinearMap.ker (LinearMap.pi fun j : {j : SymbolIndex c η θ d // j.tree.IsProper} =>
    (LinearMap.proj j.val).comp (gradeSymbolFamily a c η hc θ hχ d W))

lemma primitiveSpace_mk_iff (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)
    (f : sourceFiltration a c η hc θ d W) :
    (Submodule.Quotient.mk f : SourceAssociatedGrade a c η hc θ d W)∈
      primitiveSpace a c η hc θ hχ d W ↔
      f.val∈properSourceFiltration a c η hc θ d (W+1) := by
  rw [proper_next_iff_symbols_zero a c η hc θ hχ d W f]
  change (fun j : {j : SymbolIndex c η θ d // j.tree.IsProper} =>
    symbolFamily a c η hc θ hχ d W f j.val)=0 ↔ _
  constructor
  · intro h j hp
    exact congrFun h ⟨j,hp⟩
  · intro h
    funext j
    exact h j.val j.property

end ElementaryPositivity.RawShuffle

end

end OAI
