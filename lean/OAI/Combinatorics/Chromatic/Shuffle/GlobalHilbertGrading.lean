import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.HomogeneousBasisFibre
import OAI.Combinatorics.Chromatic.Shuffle.UnitalOriginalDegree

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def globalOriginalComponent (k : SlopeWeight c η hc θ) (ℓ : ℤ) :
    Module.End ℚ (UnitalShuffle a c η hc θ) :=
  (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k).comp
    ((unitalAssociatedComponent a c η hc θ k.1.val k.2 ℓ).comp
      (DirectSum.component ℚ _ (unitalComponent a c η hc θ) k))

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma globalOriginalComponent_lof (k : SlopeWeight c η hc θ) (ℓ : ℤ)
    (x : unitalComponent a c η hc θ k) :
    globalOriginalComponent a c η hc θ k ℓ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x)=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k
        (unitalAssociatedComponent a c η hc θ k.1.val k.2 ℓ x) := by
  simp only [globalOriginalComponent,LinearMap.comp_apply,DirectSum.component.lof_self]

lemma globalOriginalComponent_of_mem {k l : SlopeWeight c η hc θ} {m : ℤ}
    {x : UnitalShuffle a c η hc θ} (hx : x∈globalOriginalHomogeneous a c η hc θ l m) (n : ℤ) :
    globalOriginalComponent a c η hc θ k n x=if (l,m)=(k,n) then x else 0 := by
  obtain ⟨y,hy,rfl⟩:=hx
  by_cases hl : l=k
  · subst l
    rw [globalOriginalComponent_lof]
    have hy' := (mem_unitalOriginalHomogeneous a c η hc θ k.1.val k.2 m y).mp hy
    rw [←hy',unitalAssociatedComponent_twice]
    by_cases h : n=m
    · subst n
      simp [hy']
    · simp only [ite_eq_right h,Prod.mk.injEq,true_and,Ne.symm h,ite_false,map_zero]
  · simp only [globalOriginalComponent,LinearMap.comp_apply,DirectSum.component.of,
      map_zero,Prod.mk.injEq,hl,false_and,ite_false,dite_false]

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma unitalOriginalHomogeneous_range (d : I → ℕ) (W ℓ : ℤ) :
    unitalOriginalHomogeneous a c η hc θ d W ℓ=
      LinearMap.range (unitalAssociatedComponent a c η hc θ d W ℓ) := by
  ext x
  rw [mem_unitalOriginalHomogeneous]
  constructor
  · intro h; exact ⟨x,h⟩
  · rintro ⟨y,rfl⟩
    rw [unitalAssociatedComponent_twice,ite_eq_left rfl]

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma unitalOriginalHomogeneous_finite (d : I → ℕ) (W ℓ : ℤ) :
    Module.Finite ℚ (unitalOriginalHomogeneous a c η hc θ d W ℓ) := by
  let : Module.Finite ℚ (LinearMap.range (componentB a (slope c η) d ℓ)) := gradeB_finite a (slope c η) d ℓ
  rw [unitalOriginalHomogeneous_range]
  exact LinearFiltration.homogeneousMap_finite _ _ (componentB a (slope c η) d ℓ)
    (componentB_idempotent a (slope c η) d ℓ)
    (unitalSourceFiltration_component_mem a c η hc θ d W ℓ)
    (unitalSourceFiltration_component_mem a c η hc θ d (W+1) ℓ)

lemma globalOriginalComponent_range (k : SlopeWeight c η hc θ) (ℓ : ℤ) :
    LinearMap.range (globalOriginalComponent a c η hc θ k ℓ)=globalOriginalHomogeneous a c η hc θ k ℓ := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    refine ⟨unitalAssociatedComponent a c η hc θ k.1.val k.2 ℓ
      (DirectSum.component ℚ _ (unitalComponent a c η hc θ) k x),?_,rfl⟩
    rw [unitalOriginalHomogeneous_range]
    exact ⟨_,rfl⟩
  · intro x hx
    exact ⟨x,(globalOriginalComponent_of_mem a c η hc θ hx ℓ).trans (ite_eq_left rfl)⟩

lemma globalOriginalComponent_finite (k : SlopeWeight c η hc θ) (ℓ : ℤ) :
    Module.Finite ℚ (LinearMap.range (globalOriginalComponent a c η hc θ k ℓ)) := by
  rw [globalOriginalComponent_range]
  let := unitalOriginalHomogeneous_finite a c η hc θ k.1.val k.2 ℓ
  exact Module.Finite.map _ _
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

abbrev StringPBWIndex := PBWWord a c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val)

noncomputable def stringPBWGrade (l : StringPBWIndex a c η hc θ) : SlopeWeight c η hc θ × ℤ :=
  (wordWeight c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val) l.val,
   wordPolynomialDegree a c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val)
     (globalStringPolynomialDegree a c η hc θ) l.val)

abbrev StringPBWGradedIndex (k : SlopeWeight c η hc θ) (m : ℤ) :=
  {l : StringPBWIndex a c η hc θ // stringPBWGrade a c η hc θ l=(k,m)}

lemma stringPBWBasis_component (k : SlopeWeight c η hc θ ×ℤ) (l : StringPBWIndex a c η hc θ) :
    globalOriginalComponent a c η hc θ k.1 k.2 (globalStringPBWBasis a c η hc θ l)=
      if stringPBWGrade a c η hc θ l=k then globalStringPBWBasis a c η hc θ l else 0 := by
  rcases k with ⟨k,n⟩
  simpa [stringPBWGrade] using
    globalOriginalComponent_of_mem a c η hc θ (globalStringPBWBasis_original a c η hc θ l) n

noncomputable def stringPBWGradedBasis (k : SlopeWeight c η hc θ) (m : ℤ) :
    Module.Basis (StringPBWGradedIndex a c η hc θ k m) ℚ
      (LinearMap.range (globalOriginalComponent a c η hc θ k m)) :=
  ElementaryPositivity.homogeneousBasisFibre (globalStringPBWBasis a c η hc θ)
    (stringPBWGrade a c η hc θ) (fun k=>globalOriginalComponent a c η hc θ k.1 k.2)
    (stringPBWBasis_component a c η hc θ) (k,m)

lemma stringPBWGradedIndex_finite (k : SlopeWeight c η hc θ) (m : ℤ) :
    Finite (StringPBWGradedIndex a c η hc θ k m) := by
  let := globalOriginalComponent_finite a c η hc θ k m
  exact Module.Finite.finite_basis (stringPBWGradedBasis a c η hc θ k m)

lemma globalOriginalComponent_rank (k : SlopeWeight c η hc θ) (m : ℤ) :
    Module.finrank ℚ (LinearMap.range (globalOriginalComponent a c η hc θ k m))=
      Module.finrank ℚ (unitalOriginalHomogeneous a c η hc θ k.1.val k.2 m) := by
  rw [globalOriginalComponent_range]
  exact (Submodule.equivMapOfInjective (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k)
    (DirectSum.of_injective k) (unitalOriginalHomogeneous a c η hc θ k.1.val k.2 m)).finrank_eq.symm

theorem stringPBWHilbert_coefficient (k : SlopeWeight c η hc θ) (m : ℤ) :
    Module.finrank ℚ (unitalOriginalHomogeneous a c η hc θ k.1.val k.2 m)=
      Nat.card (StringPBWGradedIndex a c η hc θ k m) := by
  rw [←globalOriginalComponent_rank]
  let := stringPBWGradedIndex_finite a c η hc θ k m
  let := Fintype.ofFinite (StringPBWGradedIndex a c η hc θ k m)
  rw [Module.finrank_eq_card_basis (stringPBWGradedBasis a c η hc θ k m),Nat.card_eq_fintype_card]
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

omit [Fact (SlopeEulerSymmetric a c η θ)] in
lemma unitalOriginalNonzero_rank (d : I → ℕ) (hd : d≠0) (W k : ℤ) :
    Module.finrank ℚ (unitalOriginalHomogeneous a c η hc θ d W k)=
      Module.finrank ℚ (LinearMap.range (associatedComponent a c η hc θ d W k)) := by
  rw [unitalOriginalHomogeneous_range]
  let e := unitalGradeNonzeroEquiv a c η hc θ d hd W
  have E : (LinearMap.range (unitalAssociatedComponent a c η hc θ d W k)).map e.toLinearMap=
      LinearMap.range (associatedComponent a c η hc θ d W k) := by
    apply le_antisymm
    · rintro _ ⟨_,⟨y,rfl⟩,rfl⟩
      exact ⟨e y,(unitalAssociatedComponent_nonzero a c η hc θ d hd W k y).symm⟩
    · rintro _ ⟨y,rfl⟩
      refine ⟨unitalAssociatedComponent a c η hc θ d W k (e.symm y),⟨e.symm y,rfl⟩,?_⟩
      exact (unitalAssociatedComponent_nonzero a c η hc θ d hd W k (e.symm y)).trans
        (congrArg (associatedComponent a c η hc θ d W k) (e.apply_symm_apply y))
  exact (e.finrank_map_eq _).symm.trans (congrArg (fun N : Submodule ℚ _=>Module.finrank ℚ N) E)

theorem sourcePBWHilbert_coefficient (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ)
    (k : ℤ) (n : ℕ) (hn : 2*k+eulerForm a d d < -interaction a d d+n) :
    Module.finrank ℚ (gradeB a (slope c η) d k)=
      ∑ j∈Finset.range n, Nat.card (StringPBWGradedIndex a c η hc θ
        (⟨d,Or.inr hs⟩,-interaction a d d+j) k) := by
  rw [←sourceHilbert_filtration a c η hc θ d hd hs k n hn]
  apply Finset.sum_congr rfl
  intro j hj
  rw [←unitalOriginalNonzero_rank a c η hc θ d hd]
  exact stringPBWHilbert_coefficient a c η hc θ (⟨d,Or.inr hs⟩,-interaction a d d+j) k
end ElementaryPositivity.RawShuffle

end

end OAI
