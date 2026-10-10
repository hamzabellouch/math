import Mathlib
import OAI.Geometry.PrescribedPotential.BoundedBilinearCompletion
import OAI.Geometry.PrescribedPotential.GlobalProduct
import OAI.Geometry.PrescribedPotential.GlobalStrongEmbedding
import OAI.Geometry.PrescribedPotential.PatchCutoffs

namespace OAI

/-! Completed Product. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical BoundedContinuousFunction
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]

def Smooth.mulBilinear : Smooth A →ₗ[ℝ] Smooth A →ₗ[ℝ] Smooth A where
  toFun f :=
    { toFun := f.mul
      map_add' h l := by ext x; change f x*(h x+l x) = _; exact mul_add _ _ _
      map_smul' c h := by ext x; change f x*(c • h x) = c • (f x*h x); simp [mul_left_comm] }
  map_add' f h := by ext l x; change (f x+h x)*l x = _; exact add_mul _ _ _
  map_smul' c f := by ext h x; change (c • f x)*h x = c • (f x*h x); simp [mul_assoc]

namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

 
def product (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    D.localizers.Sobolev (k : ℝ) →L[ℝ]
      D.localizers.Sobolev (k : ℝ) →L[ℝ] D.localizers.Sobolev (k : ℝ) :=
  BoundedBilinearCompletion.extend (D.localizers.embed (k : ℝ))
    (D.localizers.embed_dense (k : ℝ)) Smooth.mulBilinear
    (D.smooth_product_bound k hk).choose_spec.2

lemma product_embed (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (f h : Smooth A) :
    D.product k hk (D.localizers.embed (k : ℝ) f) (D.localizers.embed (k : ℝ) h) =
      D.localizers.embed (k : ℝ) (f.mul h) :=
  BoundedBilinearCompletion.extend_eq _ _ _ (D.smooth_product_bound k hk).choose_spec.1
    (D.smooth_product_bound k hk).choose_spec.2 f h

lemma product_strong (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (u v : D.localizers.Sobolev (k : ℝ)) :
    D.localizers.strong (k : ℝ) (D.product k hk u v) =
      D.localizers.strong (k : ℝ) u * D.localizers.strong (k : ℝ) v := by
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hf (f : Smooth A) : ∀ v,
      D.localizers.strong (k : ℝ) (D.product k hk (D.localizers.embed (k : ℝ) f) v) =
        D.localizers.strong (k : ℝ) (D.localizers.embed (k : ℝ) f)*D.localizers.strong (k : ℝ) v := by
    apply congr_fun
    apply (D.localizers.embed_dense (k : ℝ)).equalizer (by fun_prop) (by fun_prop)
    funext h
    dsimp only [Function.comp_apply]
    rw [D.product_embed, D.localizers.strong_embed _ hs, D.localizers.strong_embed _ hs,
      D.localizers.strong_embed _ hs]
    rfl
  have he : (fun u => D.localizers.strong (k : ℝ) (D.product k hk u v)) =
      (fun u => D.localizers.strong (k : ℝ) u*D.localizers.strong (k : ℝ) v) := by
    apply (D.localizers.embed_dense (k : ℝ)).equalizer (by fun_prop) (by fun_prop)
    funext f
    exact hf f v
  exact congr_fun he u

 

lemma product_contDiff (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    ContDiff ℝ ∞ (fun z : D.localizers.Sobolev (k : ℝ) × D.localizers.Sobolev (k : ℝ) =>
      D.product k hk z.1 z.2) :=
  ((D.product k hk).contDiff.comp contDiff_fst).clm_apply contDiff_snd
end GluingData
end GlobalElliptic

end
end

end OAI
