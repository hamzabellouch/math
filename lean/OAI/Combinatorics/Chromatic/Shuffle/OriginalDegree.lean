import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FiltrationHomogeneousRank
import OAI.Combinatorics.Chromatic.Shuffle.PrimitiveSpace
import OAI.Combinatorics.Chromatic.Walls.LinearFiltrationFinite

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma properSourceFiltration_component_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W ℓ : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈properSourceFiltration a c η hc θ d W) :
    componentB a (SlopeArithmetic.slope c η) d ℓ f∈properSourceFiltration a c η hc θ d W := by
  intro T ho hp hs hd k z hw
  subst d
  rw [SplitTree.restrictionTest_component]
  split_ifs
  · exact hf T ho hp hs rfl k z hw
  · rfl

noncomputable def associatedComponent (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W ℓ : ℤ) : Module.End ℚ (SourceAssociatedGrade a c η hc θ d W) :=
  LinearFiltration.map _ _ _ _ (componentB a (SlopeArithmetic.slope c η) d ℓ)
    (fun f hf=>sourceFiltration_component_mem a c η hc θ d W ℓ f hf)
    (fun f hf=>sourceFiltration_component_mem a c η hc θ d (W+1) ℓ f hf)

lemma associatedComponent_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W ℓ : ℤ) (f : sourceFiltration a c η hc θ d W) :
    associatedComponent a c η hc θ d W ℓ (Submodule.Quotient.mk f)=
      (Submodule.Quotient.mk ⟨componentB a (SlopeArithmetic.slope c η) d ℓ f.val,
        sourceFiltration_component_mem a c η hc θ d W ℓ f.val f.property⟩ :
      SourceAssociatedGrade a c η hc θ d W) := rfl

lemma associatedComponent_twice (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W ℓ m : ℤ) (f : SourceAssociatedGrade a c η hc θ d W) :
    associatedComponent a c η hc θ d W ℓ (associatedComponent a c η hc θ d W m f)=
      if ℓ=m then associatedComponent a c η hc θ d W m f else 0 := by
  classical
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    simp only [associatedComponent_mk]
    split_ifs with h
    · apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact (componentB_componentB a _ d ℓ m f.val).trans (ite_eq_left h)
    · rw [show (0 : SourceAssociatedGrade a c η hc θ d W)=Submodule.Quotient.mk 0 from rfl]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact (componentB_componentB a _ d ℓ m f.val).trans (ite_eq_right h)

lemma associatedComponent_finite (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W ℓ : ℤ) :
    Module.Finite ℚ (LinearMap.range (associatedComponent a c η hc θ d W ℓ)) := by
  let : Module.Finite ℚ (LinearMap.range (componentB a (SlopeArithmetic.slope c η) d ℓ)) :=
    gradeB_finite a _ d ℓ
  exact LinearFiltration.map_range_finite _ _ _ _ _

lemma associatedComponent_negative (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W ℓ : ℤ) (hℓ : ℓ<0) :
    associatedComponent a c η hc θ d W ℓ=0 := by
  apply LinearFiltration.map_eq_zero
  intro f _
  rw [componentB_negative a _ d ℓ hℓ]
  exact (sourceFiltration a c η hc θ d (W+1)).zero_mem

lemma associatedComponent_upper (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hθ : SlopeArithmetic.slope c η d=θ)
    (W ℓ : ℤ) (hw : 2*ℓ+eulerForm a d d<W) :
    associatedComponent a c η hc θ d W ℓ=0 := by
  apply LinearFiltration.map_eq_zero
  intro f hf
  have hmem : componentB a (SlopeArithmetic.slope c η) d ℓ f∈
      gradeB a (SlopeArithmetic.slope c η) d ℓ ⊓ sourceFiltration a c η hc θ d W :=
    ⟨⟨f,rfl⟩,sourceFiltration_component_mem a c η hc θ d W ℓ f hf⟩
  rw [sourceFiltration_upper a c η hc θ d hd hθ ℓ W hw] at hmem
  rw [Submodule.mem_bot] at hmem
  rw [hmem]
  exact (sourceFiltration a c η hc θ d (W+1)).zero_mem

lemma associatedComponent_finite_decomposition (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) (W : ℤ)
    (f : SourceAssociatedGrade a c η hc θ d W) :
    ∃ s : Finset ℤ,(∀ ℓ∉s,associatedComponent a c η hc θ d W ℓ f=0) ∧
      (∑ ℓ∈s,associatedComponent a c η hc θ d W ℓ f)=f := by
  classical
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    obtain ⟨s,hs,he⟩:=componentB_finite_decomposition a (SlopeArithmetic.slope c η) d f.val
    refine ⟨s,?_,?_⟩
    · intro ℓ hℓ
      rw [associatedComponent_mk]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change componentB a _ d ℓ f.val∈sourceFiltration a c η hc θ d (W+1)
      rw [hs ℓ hℓ]
      exact Submodule.zero_mem _
    · let g : ℤ → sourceFiltration a c η hc θ d W := fun ℓ=>
        ⟨componentB a (SlopeArithmetic.slope c η) d ℓ f.val,
          sourceFiltration_component_mem a c η hc θ d W ℓ f.val f.property⟩
      change (∑ ℓ∈s,(nextFiltration a c η hc θ d W).mkQ (g ℓ))=_
      rw [←map_sum]
      apply congrArg (nextFiltration a c η hc θ d W).mkQ
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using he

lemma associatedComponent_primitive (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W ℓ : ℤ)
    (f : SourceAssociatedGrade a c η hc θ d W)
    (hf : f∈primitiveSpace a c η hc θ hχ d W) :
    associatedComponent a c η hc θ d W ℓ f∈primitiveSpace a c η hc θ hχ d W := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [associatedComponent_mk]
    apply (primitiveSpace_mk_iff a c η hc θ hχ d W _).mpr
    exact properSourceFiltration_component_mem a c η hc θ d (W+1) ℓ f.val
      ((primitiveSpace_mk_iff a c η hc θ hχ d W f).mp hf)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)

noncomputable def originalFilteredPiece (d : I → ℕ) (k W : ℤ) :
    Submodule ℚ (gradeB a (slope c η) d k) :=
  (sourceFiltration a c η hc θ d W).comap (gradeB a (slope c η) d k).subtype

lemma originalFilteredPiece_antitone (d : I → ℕ) (k : ℤ) :
    Antitone (originalFilteredPiece a c η hc θ d k) := by
  intro U V h
  exact Submodule.comap_mono (sourceFiltration_antitone a c η hc θ d h)

lemma originalFilteredPiece_lower (d : I → ℕ) (k : ℤ) :
    originalFilteredPiece a c η hc θ d k (-interaction a d d)=⊤ := by
  unfold originalFilteredPiece
  rw [sourceFiltration_lower,Submodule.comap_top]

lemma originalFilteredPiece_upper (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ)
    (k W : ℤ) (hW : 2*k+eulerForm a d d<W) :
    originalFilteredPiece a c η hc θ d k W=⊥ := by
  apply bot_unique
  intro x hx
  apply Subtype.ext
  have H := sourceFiltration_upper a c η hc θ d hd hs k W hW
  have hx' : x.val∈gradeB a (slope c η) d k ⊓ sourceFiltration a c η hc θ d W := ⟨x.property,hx⟩
  rw [H] at hx'
  exact hx'

lemma associatedComponent_rank_eq (d : I → ℕ) (k W : ℤ) :
    Module.finrank ℚ (LinearMap.range (associatedComponent a c η hc θ d W k))=
      Module.finrank ℚ (LinearFiltration.Grade (originalFilteredPiece a c η hc θ d k W)
        (originalFilteredPiece a c η hc θ d k (W+1))) := by
  let : Module.Finite ℚ (LinearMap.range (componentB a (slope c η) d k)) := gradeB_finite a (slope c η) d k
  exact LinearFiltration.homogeneousGrade_rank_eq _ _ (componentB a (slope c η) d k)
    (componentB_idempotent a (slope c η) d k)
    (sourceFiltration_component_mem a c η hc θ d W k)
    (sourceFiltration_component_mem a c η hc θ d (W+1) k)
    (sourceFiltration_antitone a c η hc θ d (show W≤W+1 by omega))

theorem sourceHilbert_filtration (d : I → ℕ) (hd : d≠0) (hs : slope c η d=θ)
    (k : ℤ) (n : ℕ) (hn : 2*k+eulerForm a d d < -interaction a d d+n) :
    (∑ j∈Finset.range n, Module.finrank ℚ
      (LinearMap.range (associatedComponent a c η hc θ d (-interaction a d d+j) k)))=
    Module.finrank ℚ (gradeB a (slope c η) d k) := by
  let := gradeB_finite a (slope c η) d k
  conv_lhs =>
    arg 2
    ext j
    rw [associatedComponent_rank_eq]
  exact finiteFiltration_rank_total (originalFilteredPiece a c η hc θ d k)
    (originalFilteredPiece_antitone a c η hc θ d k) (-interaction a d d) n
    (originalFilteredPiece_lower a c η hc θ d k)
    (originalFilteredPiece_upper a c η hc θ d hd hs k _ hn)
end ElementaryPositivity.RawShuffle

end

end OAI
