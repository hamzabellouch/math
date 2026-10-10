import OAI.Analysis.KadisonKastler.Algebra
import Mathlib.Analysis.InnerProductSpace.ProdL2

namespace OAI

/-! # A pair of representations on its Hilbert direct sum -/

namespace KadisonKastler

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def hilbertPairOperator (a : E →L[ℂ] E) (b : F →L[ℂ] F) :
    WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap.comp
    ((a.prodMap b).comp (WithLp.prodContinuousLinearEquiv 2 ℂ E F).toContinuousLinearMap)

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem hilbertPairOperator_fst (a : E →L[ℂ] E) (b : F →L[ℂ] F)
    (x : WithLp 2 (E × F)) : (hilbertPairOperator a b x).fst = a x.fst := rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem hilbertPairOperator_snd (a : E →L[ℂ] E) (b : F →L[ℂ] F)
    (x : WithLp 2 (E × F)) : (hilbertPairOperator a b x).snd = b x.snd := rfl

theorem hilbertPairOperator_star (a : E →L[ℂ] E) (b : F →L[ℂ] F) :
    star (hilbertPairOperator a b) = hilbertPairOperator (star a) (star b) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((hilbertPairOperator a b).adjoint x) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (a y.fst) x.fst + inner ℂ (b y.snd) x.snd =
    inner ℂ y.fst (a.adjoint x.fst) + inner ℂ y.snd (b.adjoint x.snd)
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]

variable {A : Type*} [Semiring A] [StarRing A] [_root_.Algebra ℂ A]

def hilbertPairRepresentation (ρ : A →⋆ₐ[ℂ] (E →L[ℂ] E))
    (σ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) :
    A →⋆ₐ[ℂ] (WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F)) where
  toFun a := hilbertPairOperator (ρ a) (σ a)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ E F).injective
    change (ρ 1 x.fst, σ 1 x.snd) = (x.fst, x.snd)
    simp only [map_one, one_apply_eq_self]
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ E F).injective
    change (ρ (a * b) x.fst, σ (a * b) x.snd) =
      (ρ a (ρ b x.fst), σ a (σ b x.snd))
    simp only [map_mul, mul_apply_eq_comp]
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ E F).injective
    change (ρ 0 x.fst, σ 0 x.snd) = (0, 0)
    simp only [map_zero, zero_apply]
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ E F).injective
    change (ρ (a + b) x.fst, σ (a + b) x.snd) =
      (ρ a x.fst + ρ b x.fst, σ a x.snd + σ b x.snd)
    simp only [map_add, add_apply]
  commutes' r := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ E F).injective
    change (ρ (algebraMap ℂ A r) x.fst, σ (algebraMap ℂ A r) x.snd) =
      (r • x.fst, r • x.snd)
    rw [AlgHomClass.commutes ρ, AlgHomClass.commutes σ]
    rfl
  map_star' a := by
    rw [map_star, map_star, hilbertPairOperator_star]

end

end KadisonKastler

end OAI
