import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.SobolevProduct

namespace OAI

/-! Global Strong Embedding. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped SchwartzMap ContDiff Classical BoundedContinuousFunction
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]

def Smooth.bounded (f : Smooth A) : X →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact ⟨f, f.continuous⟩

def Smooth.boundedLinear : Smooth A →ₗ[ℝ] (X →ᵇ ℂ) where
  toFun := Smooth.bounded
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

namespace Localizers
variable (D : Localizers A ι)

lemma smooth_bounded_estimate (s : ℝ) (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Smooth A, ‖f.bounded‖ ≤ C*‖D.embed s f‖ := by
  let B := ‖strongEmbedding (E := EC d) s hs‖
  refine ⟨(Fintype.card ι : ℝ)*B, mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _), fun f => ?_⟩
  apply (BoundedContinuousFunction.norm_le (mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (norm_nonneg _))).mpr
  intro x
  change ‖f x‖ ≤ _
  have he : f x = ∑ p : ι, D.weight p x*f x := by rw [← Finset.sum_mul, D.sum_one, one_mul]
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p : ι, B*‖D.embed s f‖ := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hx : x ∈ tsupport (D.weight p : X → ℂ)
      · have hxs := D.support_sub p hx
        have hp := strongEmbedding_norm s hs
          (schwartzCoord s (localize A (D.index p) (D.weight p) (D.support_sub p) f))
          (A.euclideanChart (D.index p) x)
        rw [strongEmbedding_schwartz] at hp
        change ‖localizeFun A (D.index p) (D.weight p) f (A.euclideanChart (D.index p) x)‖ ≤ _ at hp
        rw [localizeFun_apply A _ _ ((A.euclideanChart (D.index p)).mapsTo hxs),
          (A.euclideanChart (D.index p)).left_inv hxs] at hp
        exact hp.trans (mul_le_mul_of_nonneg_left
          (norm_le_pi_norm (D.coordinates s f) p) (norm_nonneg _))
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero]
        positivity
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

def strong (s : ℝ) : D.Sobolev s →L[ℝ] (X →ᵇ ℂ) :=
  Smooth.boundedLinear.extendOfNorm (D.embed s)

lemma strong_embed (s : ℝ) (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*s) (f : Smooth A) :
    D.strong s (D.embed s f) = f.bounded := by
  obtain ⟨C,_,hc⟩ := D.smooth_bounded_estimate s hs
  exact LinearMap.extendOfNorm_eq (D.embed_dense s) ⟨C,hc⟩ f

lemma strong_localized (s : ℝ) (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*s)
    (u : D.Sobolev s) (p : ι) (y : EC d) :
    strongEmbedding s hs (u.val p) y = if y ∈ (A.euclideanChart (D.index p)).target then
      D.weight p ((A.euclideanChart (D.index p)).symm y) *
        D.strong s u ((A.euclideanChart (D.index p)).symm y) else 0 := by
  have he : (fun u : D.Sobolev s => strongEmbedding s hs (u.val p) y) =
      (fun u : D.Sobolev s => if y ∈ (A.euclideanChart (D.index p)).target then
        D.weight p ((A.euclideanChart (D.index p)).symm y)*
          D.strong s u ((A.euclideanChart (D.index p)).symm y) else 0) := by
    apply (D.embed_dense s).equalizer
    · exact ((BoundedContinuousFunction.lipschitz_eval_const y).continuous.comp
        ((strongEmbedding s hs).continuous.comp ((continuous_apply p).comp continuous_subtype_val)))
    · split_ifs <;> fun_prop
    funext f
    dsimp only [Function.comp_apply]
    rw [D.strong_embed s hs]
    change strongEmbedding s hs (schwartzCoord s (localize A (D.index p)
      (D.weight p) (D.support_sub p) f)) y = _
    rw [strongEmbedding_schwartz]
    rfl
  exact congr_fun he u

lemma strong_injective (s : ℝ) (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*s) :
    Function.Injective (D.strong s) := by
  intro u v huv
  apply Subtype.ext
  funext p
  apply realize_injective s
  rw [← strongEmbedding_distribution s hs, ← strongEmbedding_distribution s hs]
  congr 1
  ext y
  rw [D.strong_localized s hs, D.strong_localized s hs, huv]
end Localizers
end GlobalElliptic

end
end

end OAI
