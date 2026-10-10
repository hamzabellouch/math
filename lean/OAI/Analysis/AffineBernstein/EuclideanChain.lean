import Mathlib
import OAI.Analysis.AffineBernstein.TubeCombination

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section EuclideanChain

lemma continuousLinearMap_euclidean_sum {k : ℕ} (L : Space k →L[ℝ] ℝ) (y : Space k) :
    L y = ∑ i : Fin k, L ((EuclideanSpace.basisFun (Fin k) ℝ) i)*y i := by
  have hr : (∑ i : Fin k, y i • (EuclideanSpace.basisFun (Fin k) ℝ) i) = y := by
    simpa only [EuclideanSpace.basisFun_repr] using (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr y
  calc
    _ = L (∑ i : Fin k, y i • (EuclideanSpace.basisFun (Fin k) ℝ) i) := congrArg L hr.symm
    _ = _ := by simp [map_sum,map_smul,mul_comm]

lemma euclidean_chain_fderiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {f : X → Space k} {φ : Space k → ℝ} {x : X}
    (hf : DifferentiableAt ℝ f x) (hφ : DifferentiableAt ℝ φ (f x)) (v : X) :
    fderiv ℝ (φ ∘ f) x v = ∑ i : Fin k,
      fderiv ℝ φ (f x) ((EuclideanSpace.basisFun (Fin k) ℝ) i)*
        fderiv ℝ (fun y => f y i) x v := by
  rw [fderiv_comp x hφ hf]
  change fderiv ℝ φ (f x) (fderiv ℝ f x v) = _
  rw [continuousLinearMap_euclidean_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hi := ((EuclideanSpace.proj i).hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  exact (congrArg (fun L : X →L[ℝ] ℝ => L v) hi).symm

end EuclideanChain

/- Euclidean norm squared of the gradient, written in the fixed orthonormal coordinate basis. -/
def euclideanGradientSquare {k : ℕ} (φ : Space k → ℝ) (s : Space k) : ℝ :=
  ∑ i : Fin k, (fderiv ℝ φ s ((EuclideanSpace.basisFun (Fin k) ℝ) i))^2

lemma euclideanGradientSquare_eq_norm {k : ℕ} (φ : Space k → ℝ) (s : Space k) :
    euclideanGradientSquare φ s = ‖fderiv ℝ φ s‖^2 := by
  have hh := (EuclideanSpace.basisFun (Fin k) ℝ).sum_sq_inner_left
    ((InnerProductSpace.toDual ℝ (Space k)).symm (fderiv ℝ φ s))
  simpa only [euclideanGradientSquare,InnerProductSpace.toDual_symm_apply,LinearIsometryEquiv.norm_map] using hh

lemma euclideanGradientSquare_nonneg {k : ℕ} (φ : Space k → ℝ) (s : Space k) :
    0 ≤ euclideanGradientSquare φ s := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma euclideanGradientSquare_zero {k : ℕ} {φ : Space k → ℝ} {s : Space k}
    (hs : s ∉ tsupport φ) : euclideanGradientSquare φ s = 0 := by
  simp [euclideanGradientSquare,fderiv_of_notMem_tsupport ℝ hs]

lemma tsupport_euclideanGradientSquare {k : ℕ} (φ : Space k → ℝ) :
    tsupport (euclideanGradientSquare φ) ⊆ tsupport φ := by
  apply closure_minimal _ isClosed_closure
  intro s hs
  by_contra hn
  exact hs (euclideanGradientSquare_zero hn)

lemma contDiff_euclideanGradientSquare {k : ℕ} {φ : Space k → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (euclideanGradientSquare φ) := by
  exact ContDiff.sum fun i _ => (((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).pow 2)

lemma compactSupport_euclideanGradientSquare {k : ℕ} {φ : Space k → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (euclideanGradientSquare φ) :=
  hc.isCompact.of_isClosed_subset isClosed_closure (tsupport_euclideanGradientSquare φ)

lemma logPullback_gradient_nonneg {k : ℕ} (φ : Space k → ℝ) (s : Space k) :
    0 ≤ logPullback (euclideanGradientSquare φ) s := by
  unfold logPullback
  split_ifs
  · exact euclideanGradientSquare_nonneg _ _
  · exact le_rfl

lemma logPullback_gradient_support {k : ℕ} {φ : Space k → ℝ} (hc : HasCompactSupport φ) :
    tsupport (logPullback (euclideanGradientSquare φ)) ⊆ expSpace '' tsupport φ := by
  apply (tsupport_logPullback_subset (compactSupport_euclideanGradientSquare hc)).trans
  exact Set.image_mono (tsupport_euclideanGradientSquare φ)

lemma logPullback_fderiv_chain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {φ : Space k → ℝ} (hφ : ContDiff ℝ ∞ φ) {q : Space k × E}
    (hq : q.1 ∈ positiveOrthant k) (v : Space k × E) :
    fderiv ℝ (fun z : Space k × E => logPullback φ z.1) q v =
      ∑ i : Fin k, fderiv ℝ φ (logSpace q.1) ((EuclideanSpace.basisFun (Fin k) ℝ) i)*
        fderiv ℝ (fun z : Space k × E => Real.log (z.1 i)) q v := by
  have he : (fun z : Space k × E => logPullback φ z.1) =ᶠ[nhds q]
      (φ ∘ fun z : Space k × E => logSpace z.1) :=
    (logPullback_eventuallyEq φ hq).comp_tendsto continuousAt_fst
  rw [he.fderiv_eq]
  exact euclidean_chain_fderiv
    (((contDiffAt_logSpace hq).comp q contDiffAt_fst).differentiableAt (by simp))
    (hφ.differentiable (by simp) _) v

end AffineBernstein
end

end OAI
