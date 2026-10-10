import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Degree

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open SplitTree
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma translationB_shuffleB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (t : ℚ) (f : B a (SlopeArithmetic.slope c η) d) (g : B a (SlopeArithmetic.slope c η) e) :
    translationB a (SlopeArithmetic.slope c η) (d+e) t (shuffleB a c η hc d e hs f g)=
      shuffleB a c η hc d e hs (translationB a (SlopeArithmetic.slope c η) d t f)
        (translationB a (SlopeArithmetic.slope c η) e t g) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    induction g using Submodule.Quotient.induction_on with
    | H g =>
      exact congrArg (destabilizingSpace a (SlopeArithmetic.slope c η) (d+e)).mkQ
        (translation_shufflePolynomial a t f g)

lemma shuffleB_leaf_degreeCut (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (hχ : eulerForm a d e=eulerForm a e d) (U V : ℤ)
    (f : B a (SlopeArithmetic.slope c η) d) (g : B a (SlopeArithmetic.slope c η) e)
    (hf : f∈degreeCutSubmodule a (SlopeArithmetic.slope c η) (.leaf d) U)
    (hg : g∈degreeCutSubmodule a (SlopeArithmetic.slope c η) (.leaf e) V) :
    shuffleB a c η hc d e hs f g∈degreeCutSubmodule a (SlopeArithmetic.slope c η) (.leaf (d+e)) (U+V) := by
  classical
  intro k hk
  change ℤ at k
  change 2*k+eulerForm a (d+e) (d+e)<U+V at hk
  change componentB a (SlopeArithmetic.slope c η) (d+e) k (shuffleB a c η hc d e hs f g)=0
  obtain ⟨s,_,hsum⟩ := componentB_finite_decomposition a (SlopeArithmetic.slope c η) d f
  obtain ⟨t,_,htsum⟩ := componentB_finite_decomposition a (SlopeArithmetic.slope c η) e g
  rw [←hsum,←htsum]
  simp only [map_sum,LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro m hm
  by_cases hm' : 2*m+eulerForm a d d<U
  · have hz : componentB a (SlopeArithmetic.slope c η) d m f=0 := hf m hm'
    rw [hz,map_zero,LinearMap.zero_apply,map_zero]
  by_cases hn' : 2*n+eulerForm a e e<V
  · have hz : componentB a (SlopeArithmetic.slope c η) e n g=0 := hg n hn'
    rw [hz,map_zero,map_zero]
  rw [componentB_on_grade a _ _ k (m+n-eulerForm a d e) _
    (shuffleB_graded a c η hc d e hs m n _ _ ⟨f,rfl⟩ ⟨g,rfl⟩)]
  apply ite_eq_right
  rw [eulerForm_add_left,eulerForm_add_right,eulerForm_add_right,←hχ] at hk
  change 2*(k : ℤ)+(eulerForm a d d+eulerForm a d e+(eulerForm a d e+eulerForm a e e))<U+V at hk
  omega

lemma sourceFiltration_leaf_degreeCut (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (hd : d≠0) (hθ : SlopeArithmetic.slope c η d=θ)
    (U : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d U) :
    f∈degreeCutSubmodule a (SlopeArithmetic.slope c η) (.leaf d) U := by
  intro k hk
  have h:=hf (.leaf d) trivial ⟨hd,hθ⟩ rfl k 0 hk
  rwa [restrictionTest_leaf_zero] at h

lemma shuffleB_translation_leaf_degreeCut (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hd : d≠0) (he : e≠0)
    (hdθ : SlopeArithmetic.slope c η d=θ) (heθ : SlopeArithmetic.slope c η e=θ)
    (hχ : eulerForm a d e=eulerForm a e d) (U V : ℤ)
    (f : B a (SlopeArithmetic.slope c η) d) (g : B a (SlopeArithmetic.slope c η) e)
    (hf : f∈sourceFiltration a c η hc θ d U) (hg : g∈sourceFiltration a c η hc θ e V)
    (t : ℚ) :
    translationB a (SlopeArithmetic.slope c η) (d+e) t
      (shuffleB a c η hc d e (hdθ.trans heθ.symm) f g)∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) (.leaf (d+e)) (U+V) := by
  rw [translationB_shuffleB]
  exact shuffleB_leaf_degreeCut a c η hc d e _ hχ U V _ _
    (sourceFiltration_leaf_degreeCut a c η hc θ d hd hdθ U _
      (sourceFiltration_translation_mem a c η hc θ d U f hf t))
    (sourceFiltration_leaf_degreeCut a c η hc θ e he heθ V _
      (sourceFiltration_translation_mem a c η hc θ e V g hg t))

end ElementaryPositivity.RawShuffle

end

end OAI
