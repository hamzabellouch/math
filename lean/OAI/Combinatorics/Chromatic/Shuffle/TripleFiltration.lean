import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.TensorFiltration

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
lemma additiveTensorFiltration_top (F : ℤ → Submodule K M) (G : ℤ → Submodule K N)
    (U V : ℤ) (hF : F U=⊤) (hG : G V=⊤) : additiveTensorFiltration F G (U+V)=⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    exact tmul_mem_additiveTensorFiltration F G (le_refl _) (hF ▸ trivial) (hG ▸ trivial)
  | add x y hx hy => exact (additiveTensorFiltration F G (U+V)).add_mem hx hy
end ElementaryPositivity.LinearDetection

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def sourceTripleFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e f : I → ℕ) (W : ℤ) :
    Submodule ℚ ((B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e)⊗[ℚ]
      B a (SlopeArithmetic.slope c η) f) :=
  additiveTensorFiltration (sourceTensorFiltration a c η hc θ d e) (sourceFiltration a c η hc θ f) W

noncomputable def indexedTensorRestriction (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (j : RestrictionIndex c η θ d × RestrictionIndex c η θ e) :=
  TensorProduct.map (indexedRestriction a c η hc θ d j.1) (indexedRestriction a c η hc θ e j.2)

lemma sourceTensorFiltration_eq_testFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    sourceTensorFiltration a c η hc θ d e W=testFiltration (indexedTensorRestriction a c η hc θ d e)
      (fun j=>j.1.weight a+j.2.weight a) W := by
  ext x
  rw [sourceTensorFiltration_iff,mem_testFiltration]
  constructor
  · exact fun h j=>h j.1 j.2
  · exact fun h i j=>h (i,j)

lemma sourceTensorFiltration_lower (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) :
    sourceTensorFiltration a c η hc θ d e (-interaction a d d+-interaction a e e)=⊤ :=
  additiveTensorFiltration_top _ _ _ _ (sourceFiltration_lower a c η hc θ d)
    (sourceFiltration_lower a c η hc θ e)

theorem sourceTripleFiltration_iff (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e f : I → ℕ) (W : ℤ)
    (x : (B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e)⊗[ℚ]
      B a (SlopeArithmetic.slope c η) f) :
    x∈sourceTripleFiltration a c η hc θ d e f W ↔
      ∀ i : RestrictionIndex c η θ d, ∀ j : RestrictionIndex c η θ e, ∀ k : RestrictionIndex c η θ f,
        i.weight a+j.weight a+k.weight a<W → TensorProduct.map
          (TensorProduct.map (indexedRestriction a c η hc θ d i) (indexedRestriction a c η hc θ e j))
          (indexedRestriction a c η hc θ f k) x=0 := by
  have hd := funext (sourceTensorFiltration_eq_testFiltration a c η hc θ d e)
  have hf := funext (sourceFiltration_eq_testFiltration a c η hc θ f)
  unfold sourceTripleFiltration
  rw [hd,hf]
  have ht := additiveTensorFiltration_iff_tests
    (indexedTensorRestriction a c η hc θ d e) (indexedRestriction a c η hc θ f)
    (fun j=>j.1.weight a+j.2.weight a) (RestrictionIndex.weight a)
    (-interaction a d d+-interaction a e e) (-interaction a f f)
    (by rw [←hd,sourceTensorFiltration_lower]) (by rw [←hf,sourceFiltration_lower]) W x
  apply ht.trans
  constructor
  · exact fun h i j k=>h (i,j) k
  · exact fun h ij k=>h ij.1 ij.2 k

lemma triple_leading_restrictions_detect (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e f : I → ℕ) (W : ℤ)
    (x : (B a (SlopeArithmetic.slope c η) d⊗[ℚ]B a (SlopeArithmetic.slope c η) e)⊗[ℚ]
      B a (SlopeArithmetic.slope c η) f)
    (hx : x∈sourceTripleFiltration a c η hc θ d e f W)
    (h : ∀ i : RestrictionIndex c η θ d, ∀ j : RestrictionIndex c η θ e, ∀ k : RestrictionIndex c η θ f,
      i.weight a+j.weight a+k.weight a=W → TensorProduct.map
        (TensorProduct.map (indexedRestriction a c η hc θ d i) (indexedRestriction a c η hc θ e j))
        (indexedRestriction a c η hc θ f k) x=0) :
    x∈sourceTripleFiltration a c η hc θ d e f (W+1) := by
  rw [sourceTripleFiltration_iff] at hx ⊢
  intro i j k hijk
  by_cases hw : i.weight a+j.weight a+k.weight a=W
  · exact h i j k hw
  · exact hx i j k (by omega)

end ElementaryPositivity.RawShuffle

end

end OAI
