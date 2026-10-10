import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.CanonicalCard

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma dimensionCast_eq_castS {d e : I → ℕ} (h : d=e) (f : S d) :
    dimensionCast h f = castS h f := by subst e; rfl

theorem restrict_destabilizing_shuffle (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e α β : I → ℕ} (h : d+e=α+β) (f : S d) (g : S e) (u : Cut α β)
    (hd : d≠0) (hα : slope c η α = slope c η β)
    (hμ : slope c η d > slope c η (α+β)) :
    quotientTensor a (slope c η) α β
      (restrictTensor u (dimensionCast h (shufflePolynomial a f g))) = 0 := by
  rw [dimensionCast_eq_castS]
  apply quotient_crossTensor_cancel
  let s : Pack (A:=fun i=>Fin ((α+β) i)) := fun _=>Finset.univ
  let R : Realization (α+β) s := defaultRealization (by intro i; simp [s])
  rw [cleared_restrictTensor a h f g R u, map_smul]
  rw [quotient_gridTensor_zero a c η hc f g _ _ _ hd hα]
  · simp
  · rwa [slope_add_same c η hc hα] at hμ

theorem restriction_kills_destabilizingSpace (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) {d e : I → ℕ} (hs : slope c η d = slope c η e)
    (u : Cut d e) {f : S (d+e)} (hf : f ∈ destabilizingSpace a (slope c η) (d+e)) :
    quotientTensor a (slope c η) d e (restrictTensor u f) = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨α,β,h,F,G,hα,hβ,hμ,rfl⟩ := hf
    exact restrict_destabilizing_shuffle a c η hc h F G u hα hs hμ
  | zero => simp
  | add f g hf hg ihf ihg => simp only [map_add,ihf,ihg,add_zero]
  | smul r f hf ih => simp only [map_smul,ih,smul_zero]

noncomputable def restrictionB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : slope c η d = slope c η e) (u : Cut d e) :
    B a (slope c η) (d+e) →ₐ[ℚ] B a (slope c η) d ⊗[ℚ] B a (slope c η) e :=
  Ideal.Quotient.liftₐ (destabilizingIdeal a (slope c η) (d+e))
    ((quotientTensor a (slope c η) d e).comp (restrictTensorAlg u))
    (by intro f hf; exact restriction_kills_destabilizingSpace a c η hc hs u hf)

@[simp] lemma restrictionB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : slope c η d = slope c η e) (u : Cut d e) (f : S (d+e)) :
    restrictionB a c η hc hs u (quotientAlg a (slope c η) (d+e) f) =
      quotientTensor a (slope c η) d e (restrictTensor u f) := rfl

noncomputable def restrictionRelativeB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : slope c η d = slope c η e) (u : Cut d e) :
    B a (slope c η) (d+e) →ₐ[ℚ] Polynomial (B a (slope c η) d ⊗[ℚ] B a (slope c η) e) :=
  (relativeTaylorB a (slope c η) d e).comp (restrictionB a c η hc hs u)

lemma restrictionRelativeB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : slope c η d = slope c η e) (u : Cut d e) (f : S (d+e)) :
    restrictionRelativeB a c η hc hs u (quotientAlg a (slope c η) (d+e) f) =
      Polynomial.map (quotientTensor a (slope c η) d e).toRingHom
        (relativeTaylor d e (restrictTensor u f)) := by
  rw [relativeTaylor_quotient]
  rfl

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

inductive SplitTree (I : Type u) where
  | leaf (d : I → ℕ)
  | node (l r : SplitTree I)

namespace SplitTree

@[reducible] def dim : SplitTree I → I → ℕ
  | .leaf d => d
  | .node l r => l.dim + r.dim

@[reducible] def OnSlope (c η : I → ℝ) (θ : ℝ) : SplitTree I → Prop
  | .leaf d => d ≠ 0 ∧ slope c η d = θ
  | .node l r => l.OnSlope c η θ ∧ r.OnSlope c η θ

omit [DecidableEq I] in
lemma dim_ne_zero {T : SplitTree I} {c η : I → ℝ} {θ : ℝ} (h : T.OnSlope c η θ) :
    T.dim ≠ 0 := by
  induction T with
  | leaf d => exact h.1
  | node l r ihl ihr => exact add_ne_zero_left _ _ (ihl h.1)

omit [DecidableEq I] in
lemma slope_dim (c η : I → ℝ) (hc : ∀ i,0<c i) {θ : ℝ} {T : SplitTree I}
    (h : T.OnSlope c η θ) : slope c η T.dim = θ := by
  induction T with
  | leaf d => exact h.2
  | node l r ihl ihr =>
    have hl := ihl h.1
    have hr := ihr h.2
    exact (slope_add_same c η hc (hl.trans hr.symm)).trans hl

@[reducible] noncomputable def tensor (A : (I → ℕ) → CommAlgCat.{u} ℚ) : SplitTree I → CommAlgCat.{u} ℚ
  | .leaf d => A d
  | .node l r => CommAlgCat.of ℚ (tensor A l ⊗[ℚ] tensor A r)

noncomputable def tensorMap (A C : (I → ℕ) → CommAlgCat.{u} ℚ)
    (f : ∀ d, A d →ₐ[ℚ] C d) : (T : SplitTree I) → tensor A T →ₐ[ℚ] tensor C T
  | .leaf d => f d
  | .node l r => Algebra.TensorProduct.map (tensorMap A C f l) (tensorMap A C f r)

noncomputable def rawFamily (d : I → ℕ) : CommAlgCat.{u} ℚ := CommAlgCat.of ℚ (S d)
noncomputable def quotientFamily (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) : CommAlgCat.{u} ℚ :=
  CommAlgCat.of ℚ (B a μ d)

noncomputable def rawRestriction : (T : SplitTree I) → S T.dim →ₐ[ℚ] tensor rawFamily T
  | .leaf d => AlgHom.id ℚ (S d)
  | .node l r => (Algebra.TensorProduct.map (rawRestriction l) (rawRestriction r)).comp
      (restrictTensorAlg (firstCut l.dim r.dim))

noncomputable def quotientMap (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (T : SplitTree I) :
    tensor rawFamily T →ₐ[ℚ] tensor (quotientFamily a μ) T :=
  tensorMap rawFamily (quotientFamily a μ) (quotientAlg a μ) T

noncomputable def restrictionB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) : (T : SplitTree I) → T.OnSlope c η θ →
      B a (slope c η) T.dim →ₐ[ℚ] tensor (quotientFamily a (slope c η)) T
  | .leaf d, _ => AlgHom.id ℚ (B a (slope c η) d)
  | .node l r, h =>
    (Algebra.TensorProduct.map (restrictionB a c η hc θ l h.1)
      (restrictionB a c η hc θ r h.2)).comp
        (RawShuffle.restrictionB a c η hc
          ((slope_dim c η hc h.1).trans (slope_dim c η hc h.2).symm)
          (firstCut l.dim r.dim))

lemma restrictionB_square (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (T : SplitTree I) (h : T.OnSlope c η θ) :
    (restrictionB a c η hc θ T h).comp (quotientAlg a (slope c η) T.dim) =
      (quotientMap a (slope c η) T).comp (rawRestriction T) := by
  induction T with
  | leaf d => rfl
  | node l r ihl ihr =>
    apply AlgHom.ext
    intro f
    change (Algebra.TensorProduct.map (restrictionB a c η hc θ l h.1)
      (restrictionB a c η hc θ r h.2))
      (quotientTensor a (slope c η) l.dim r.dim (restrictTensor (firstCut l.dim r.dim) f)) =
        (Algebra.TensorProduct.map (quotientMap a (slope c η) l) (quotientMap a (slope c η) r))
          ((Algebra.TensorProduct.map (rawRestriction l) (rawRestriction r))
            (restrictTensor (firstCut l.dim r.dim) f))
    generalize restrictTensor (firstCut l.dim r.dim) f = t
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      change restrictionB a c η hc θ l h.1 (quotientAlg a (slope c η) l.dim x) ⊗ₜ[ℚ]
          restrictionB a c η hc θ r h.2 (quotientAlg a (slope c η) r.dim y) =
        quotientMap a (slope c η) l (rawRestriction l x) ⊗ₜ[ℚ]
          quotientMap a (slope c η) r (rawRestriction r y)
      exact congrArg₂ (fun x y => x ⊗ₜ[ℚ] y)
        (AlgHom.congr_fun (ihl h.1) x) (AlgHom.congr_fun (ihr h.2) y)
    | add x y hx hy => simp only [map_add,hx,hy]

lemma restrictionB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (T : SplitTree I) (h : T.OnSlope c η θ) (f : S T.dim) :
    restrictionB a c η hc θ T h (quotientAlg a (slope c η) T.dim f) =
      quotientMap a (slope c η) T (rawRestriction T f) :=
  AlgHom.congr_fun (restrictionB_square a c η hc θ T h) f

lemma restriction_kills (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (T : SplitTree I) (h : T.OnSlope c η θ) (f : S T.dim)
    (hf : f ∈ destabilizingSpace a (slope c η) T.dim) :
    quotientMap a (slope c η) T (rawRestriction T f) = 0 := by
  rw [← restrictionB_mk a c η hc θ T h f]
  have hz : quotientAlg a (slope c η) T.dim f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hf
  rw [hz,map_zero]

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
