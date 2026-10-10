import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.ComponentB

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [DecidableEq I] [∀ i,Fintype (A i)] in
lemma labeledValue_unit (s : Pack (A:=A)) :
    labeledValue (1 : S (0 : I → ℕ)) s=if s=(fun _=>∅) then 1 else 0 := by
  classical
  by_cases hs : s=(fun _=>∅)
  · subst s
    simp [labeledValue,valueAt]
  · have h : ¬∀ i,(s i).card=(0 : I → ℕ) i := by
      intro h
      exact hs (funext fun i=>Finset.card_eq_zero.mp (h i))
    simp only [labeledValue,dite_eq_right h,ite_eq_right hs]

def emptyLeftCut (s : Pack (A:=A)) : PackConvolution.Cut s :=
  fun i=>⟨(∅,s i),by simp⟩

def emptyRightCut (s : Pack (A:=A)) : PackConvolution.Cut s :=
  fun i=>⟨(s i,∅),by simp⟩

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
lemma eq_emptyLeftCut {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (h : left p=fun _=>∅) : p=emptyLeftCut s := by
  funext i
  apply Subtype.ext
  apply Prod.ext
  · exact congrFun h i
  · have hh := (p i).property.2
    change (p i).val.1 ∪ (p i).val.2=s i at hh
    have hi : (p i).val.1=∅ := congrFun h i
    simpa only [emptyLeftCut,hi,Finset.empty_union] using hh

omit [Fintype I] [DecidableEq I] [∀ i,Fintype (A i)] in
lemma eq_emptyRightCut {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (h : right p=fun _=>∅) : p=emptyRightCut s := by
  funext i
  apply Subtype.ext
  apply Prod.ext
  · have hh := (p i).property.2
    change (p i).val.1 ∪ (p i).val.2=s i at hh
    have hi : (p i).val.2=∅ := congrFun h i
    simpa only [emptyRightCut,hi,Finset.union_empty] using hh
  · exact congrFun h i

lemma shuffle_labeled_unit_left (a : I → I → ℕ) (d : I → ℕ) (f : S d)
    (s : Pack (A:=A)) :
    PackConvolution.shuffle (pairKernel a) (labeledValue (1 : S (0 : I → ℕ)))
      (labeledValue f) s=labeledValue f s := by
  classical
  unfold PackConvolution.shuffle
  rw [Finset.sum_eq_single (emptyLeftCut s)]
  · have hL : left (emptyLeftCut s)=fun _=>∅ := rfl
    have hR : right (emptyLeftCut s)=s := rfl
    rw [labeledValue_unit,ite_eq_left hL,hR]
    simp [hL,PackConvolution.kernel]
  · intro p hp hne
    have h : left p≠(fun _=>∅) := fun hh=>hne (eq_emptyLeftCut p hh)
    simp only [labeledValue_unit,ite_eq_right h,zero_mul]
  · simp

lemma shuffle_labeled_unit_right (a : I → I → ℕ) (d : I → ℕ) (f : S d)
    (s : Pack (A:=A)) :
    PackConvolution.shuffle (pairKernel a) (labeledValue f)
      (labeledValue (1 : S (0 : I → ℕ))) s=labeledValue f s := by
  classical
  unfold PackConvolution.shuffle
  rw [Finset.sum_eq_single (emptyRightCut s)]
  · have hR : right (emptyRightCut s)=fun _=>∅ := rfl
    have hL : left (emptyRightCut s)=s := rfl
    rw [labeledValue_unit,ite_eq_left hR,hL]
    simp [hR,PackConvolution.kernel]
  · intro p hp hne
    have h : right p≠(fun _=>∅) := fun hh=>hne (eq_emptyRightCut p hh)
    simp only [labeledValue_unit,ite_eq_right h,mul_zero,zero_mul]
  · simp

lemma shufflePolynomial_unit_left (a : I → I → ℕ) (d : I → ℕ) (f : S d) :
    shufflePolynomial a (1 : S (0 : I → ℕ)) f=castS (zero_add d).symm f := by
  classical
  let s : Pack (A:=fun i=>Fin ((0+d) i)) := fun _=>Finset.univ
  let r : Realization (0+d) s := defaultRealization (by intro i; simp [s])
  apply labeledValue_injective r
  dsimp only
  rw [labeledValue_shuffle,labeledValue_cast]
  exact shuffle_labeled_unit_left a d f s

lemma shufflePolynomial_unit_right (a : I → I → ℕ) (d : I → ℕ) (f : S d) :
    shufflePolynomial a f (1 : S (0 : I → ℕ))=castS (add_zero d).symm f := by
  classical
  let s : Pack (A:=fun i=>Fin ((d+0) i)) := fun _=>Finset.univ
  let r : Realization (d+0) s := defaultRealization (by intro i; simp [s])
  apply labeledValue_injective r
  dsimp only
  rw [labeledValue_shuffle,labeledValue_cast]
  exact shuffle_labeled_unit_right a d f s

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma S_zero_eq_scalar (f : S (0 : I → ℕ)) :
    f=constantCoeff f.val • (1 : S (0 : I → ℕ)) := by
  let : IsEmpty (Σi : I, Fin ((0 : I → ℕ) i)) := ⟨fun x => Fin.elim0 x.2⟩
  rw [←Algebra.algebraMap_eq_smul_one]
  apply Subtype.ext
  exact eq_C_of_isEmpty f.val

lemma destabilizingSpace_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) :
    destabilizingSpace a μ 0=⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro f ⟨u,v,h,f',g',hu,hv,_,_⟩
  exact (hu (add_eq_zero.mp h).1).elim

lemma castS_mem_destabilizing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e : I → ℕ} (h : d=e) {f : S d} (hf : f∈destabilizingSpace a μ d) :
    castS h f∈destabilizingSpace a μ e := by
  subst e
  exact hf

lemma destabilizing_shuffle_unit_left (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    {f : S d} (hf : f∈destabilizingSpace a (slope c η) d) (g : S e) :
    shufflePolynomial a f g∈destabilizingSpace a (slope c η) (d+e) := by
  rcases hs with rfl|rfl|hs
  · rw [destabilizingSpace_zero] at hf
    have hf0 : f=0 := hf
    rw [hf0,shufflePolynomial_zero_left]
    exact Submodule.zero_mem _
  · rw [S_zero_eq_scalar g,shufflePolynomial_smul_right,shufflePolynomial_unit_right]
    exact Submodule.smul_mem _ _ (castS_mem_destabilizing a _ _ hf)
  · exact destabilizing_shuffle_left a c η hc hs hf g

lemma destabilizing_shuffle_unit_right (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (f : S d) {g : S e} (hg : g∈destabilizingSpace a (slope c η) e) :
    shufflePolynomial a f g∈destabilizingSpace a (slope c η) (d+e) := by
  rcases hs with rfl|rfl|hs
  · rw [S_zero_eq_scalar f,shufflePolynomial_smul_left,shufflePolynomial_unit_left]
    exact Submodule.smul_mem _ _ (castS_mem_destabilizing a _ _ hg)
  · rw [destabilizingSpace_zero] at hg
    have hg0 : g=0 := hg
    rw [hg0,shufflePolynomial_zero_right]
    exact Submodule.zero_mem _
  · exact destabilizing_shuffle_right a c η hc hs f hg

noncomputable def shuffleBUnit (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) :
    B a (slope c η) d →ₗ[ℚ] B a (slope c η) e →ₗ[ℚ] B a (slope c η) (d+e) := by
  let J := destabilizingSpace a (slope c η) (d+e)
  let L : S d →ₗ[ℚ] B a (slope c η) e →ₗ[ℚ] B a (slope c η) (d+e) :=
    { toFun := fun f => (destabilizingSpace a (slope c η) e).mapQ J
        (shuffleLinear a d e f) (by
          intro g hg
          exact destabilizing_shuffle_unit_right a c η hc hs f hg)
      map_add' := by
        intro f g
        apply LinearMap.ext
        intro x
        induction x using Submodule.Quotient.induction_on with
        | H x => exact congrArg J.mkQ (shufflePolynomial_add_left a f g x)
      map_smul' := by
        intro r f
        apply LinearMap.ext
        intro x
        induction x using Submodule.Quotient.induction_on with
        | H x => exact congrArg J.mkQ (shufflePolynomial_smul_left a r f x) }
  exact (destabilizingSpace a (slope c η) d).liftQ L (by
    intro f hf
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro g
    induction g using Submodule.Quotient.induction_on with
    | H g =>
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (destabilizing_shuffle_unit_left a c η hc hs hf g))

@[simp] lemma shuffleBUnit_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (f : S d) (g : S e) :
    shuffleBUnit a c η hc d e hs ((destabilizingSpace a (slope c η) d).mkQ f)
      ((destabilizingSpace a (slope c η) e).mkQ g) =
    (destabilizingSpace a (slope c η) (d+e)).mkQ (shufflePolynomial a f g) := rfl

lemma shuffleBUnit_eq_shuffleB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : slope c η d=slope c η e) :
    shuffleBUnit a c η hc d e (Or.inr (Or.inr hs))=shuffleB a c η hc d e hs := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    induction g using Submodule.Quotient.induction_on with
    | H g => rfl

end ElementaryPositivity.RawShuffle

end

end OAI
