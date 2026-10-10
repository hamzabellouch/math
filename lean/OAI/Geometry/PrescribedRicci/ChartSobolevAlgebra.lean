import Mathlib
import OAI.Geometry.PrescribedPotential.BoundedBilinearCompletion
import OAI.Geometry.PrescribedPotential.SobolevReconstruction

namespace OAI

/-! Chart Sobolev Algebra. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Classical
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def schwartzProductLinear : 𝓢(E,ℂ) →ₗ[ℝ] 𝓢(E,ℂ) →ₗ[ℝ] 𝓢(E,ℂ) where
  toFun f := (SchwartzMap.smulLeftCLM ℂ f).restrictScalars ℝ |>.toLinearMap
  map_add' f g := by
    ext h x
    change (SchwartzMap.smulLeftCLM ℂ (f+g) h) x =
      (SchwartzMap.smulLeftCLM ℂ f h) x + (SchwartzMap.smulLeftCLM ℂ g h) x
    rw [SchwartzMap.smulLeftCLM_apply_apply (f+g).hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]
    simp only [add_apply,smul_eq_mul]
    ring
  map_smul' c f := by
    ext h x
    change (SchwartzMap.smulLeftCLM ℂ (c • f) h) x =
      c • (SchwartzMap.smulLeftCLM ℂ f h) x
    rw [SchwartzMap.smulLeftCLM_apply_apply (c • f).hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth]
    simp only [smul_apply,smul_eq_mul,Complex.real_smul]
    ring

def productCoord (k : ℕ) (hk : Module.finrank ℝ E < k) : L2 E →L[ℝ] L2 E →L[ℝ] L2 E :=
  BoundedBilinearCompletion.extend (schwartzCoordLinear (k:ℝ)) (schwartzCoord_dense (k:ℝ))
    schwartzProductLinear (schwartz_sobolev_product_bound k hk).choose_spec.2

lemma productCoord_schwartz (k : ℕ) (hk : Module.finrank ℝ E < k) (f g : 𝓢(E,ℂ)) :
    productCoord k hk (schwartzCoord (k:ℝ) f) (schwartzCoord (k:ℝ) g) =
      schwartzCoord (k:ℝ) (SchwartzMap.smulLeftCLM ℂ f g) :=
  BoundedBilinearCompletion.extend_eq _ (schwartzCoord_dense (k:ℝ)) _
    (schwartz_sobolev_product_bound k hk).choose_spec.1
    (schwartz_sobolev_product_bound k hk).choose_spec.2 f g

lemma productCoord_strong (k : ℕ) (hk : Module.finrank ℝ E < k)
    (hs : (Module.finrank ℝ E:ℝ) < 2*(k:ℝ)) (u v : L2 E) :
    strongEmbedding (k:ℝ) hs (productCoord k hk u v) =
      strongEmbedding (k:ℝ) hs u * strongEmbedding (k:ℝ) hs v := by
  have core (f : 𝓢(E,ℂ)) : (fun v => strongEmbedding (k:ℝ) hs
      (productCoord k hk (schwartzCoord (k:ℝ) f) v)) =
      (fun v => strongEmbedding (k:ℝ) hs (schwartzCoord (k:ℝ) f) * strongEmbedding (k:ℝ) hs v) := by
    apply (schwartzCoord_dense (k:ℝ)).equalizer (by fun_prop) (by fun_prop)
    funext g
    simp only [Function.comp_apply,productCoord_schwartz,strongEmbedding_schwartz]
    ext x
    exact SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth g x
  have he : (fun u => strongEmbedding (k:ℝ) hs (productCoord k hk u v)) =
      (fun u => strongEmbedding (k:ℝ) hs u * strongEmbedding (k:ℝ) hs v) := by
    apply (schwartzCoord_dense (k:ℝ)).equalizer (by fun_prop) (by fun_prop)
    funext f
    exact congr_fun (core f) v
  exact congr_fun he u

lemma productCoord_lower_zero_core (k : ℕ) (hk : Module.finrank ℝ E < k)
    (hs : (Module.finrank ℝ E:ℝ) < 2*(k:ℝ)) (f : 𝓢(E,ℂ)) (v : L2 E) :
    lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k) (productCoord k hk (schwartzCoord (k:ℝ) f) v) =
      multiply (strongEmbedding (k:ℝ) hs (schwartzCoord (k:ℝ) f))
        (lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k) v) := by
  have he : (fun v : L2 E => lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k)
      (productCoord k hk (schwartzCoord (k:ℝ) f) v)) =
      (fun v => multiply (strongEmbedding (k:ℝ) hs (schwartzCoord (k:ℝ) f))
        (lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k) v)) := by
    apply (schwartzCoord_dense (k:ℝ)).equalizer
      ((lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k)).continuous.comp
        (productCoord k hk (schwartzCoord (k:ℝ) f)).continuous)
      ((multiply (strongEmbedding (k:ℝ) hs (schwartzCoord (k:ℝ) f))).continuous.comp
        (lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k)).continuous)
    funext g
    simp only [Function.comp_apply,productCoord_schwartz,
      lowerCoord_schwartz,strongEmbedding_schwartz]
    exact schwartzCoord_product_zero f g
  exact congr_fun he v

lemma productCoord_lower_zero (k : ℕ) (hk : Module.finrank ℝ E < k)
    (hs : (Module.finrank ℝ E:ℝ) < 2*(k:ℝ)) (u v : L2 E) :
    lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k) (productCoord k hk u v) =
      multiply (strongEmbedding (k:ℝ) hs u) (lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k) v) := by
  have hc : Continuous (fun u : L2 E => multiply (strongEmbedding (k:ℝ) hs u)
      (lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k) v)) :=
    by
      change Continuous (fun u : L2 E => (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2
        (boundedToLinf (strongEmbedding (k:ℝ) hs u)) (lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k) v))
      exact (((ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2).continuous.comp
        (boundedToLinf.continuous.comp (strongEmbedding (k:ℝ) hs).continuous)).clm_apply continuous_const
  have he : (fun u => lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k) (productCoord k hk u v)) =
      (fun u => multiply (strongEmbedding (k:ℝ) hs u) (lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k) v)) := by
    apply (schwartzCoord_dense (k:ℝ)).equalizer
      ((lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k)).continuous.comp
        ((productCoord k hk).continuous.clm_apply continuous_const)) hc
    funext f
    exact productCoord_lower_zero_core k hk hs f v
  exact congr_fun he u

lemma strongEmbedding_lower {s t : ℝ} (hst : t ≤ s)
    (hs : (Module.finrank ℝ E:ℝ) < 2*s) (ht : (Module.finrank ℝ E:ℝ) < 2*t)
    (u : L2 E) : strongEmbedding t ht (lowerCoord s t hst u) = strongEmbedding s hs u := by
  apply boundedDistribution_injective
  rw [strongEmbedding_distribution,realize_lowerCoord,strongEmbedding_distribution]

lemma productCoord_lower (k l : ℕ) (hk : Module.finrank ℝ E < k)
    (hl : Module.finrank ℝ E < l) (hlk : l ≤ k) (u v : L2 E) :
    lowerCoord (k:ℝ) (l:ℝ) (by exact_mod_cast hlk) (productCoord k hk u v) =
      productCoord l hl (lowerCoord (k:ℝ) (l:ℝ) (by exact_mod_cast hlk) u)
        (lowerCoord (k:ℝ) (l:ℝ) (by exact_mod_cast hlk) v) := by
  have core (f : 𝓢(E,ℂ)) : (fun v => lowerCoord (k:ℝ) (l:ℝ) (by exact_mod_cast hlk)
      (productCoord k hk (schwartzCoord (k:ℝ) f) v)) =
      (fun v => productCoord l hl (lowerCoord (k:ℝ) (l:ℝ) (by exact_mod_cast hlk) (schwartzCoord (k:ℝ) f))
        (lowerCoord (k:ℝ) (l:ℝ) (by exact_mod_cast hlk) v)) := by
    apply (schwartzCoord_dense (k:ℝ)).equalizer (by fun_prop) (by fun_prop)
    funext g
    simp only [Function.comp_apply,productCoord_schwartz,lowerCoord_schwartz]
  have he : (fun u => lowerCoord (k:ℝ) (l:ℝ) (by exact_mod_cast hlk) (productCoord k hk u v)) =
      (fun u => productCoord l hl (lowerCoord (k:ℝ) (l:ℝ) (by exact_mod_cast hlk) u)
        (lowerCoord (k:ℝ) (l:ℝ) (by exact_mod_cast hlk) v)) := by
    apply (schwartzCoord_dense (k:ℝ)).equalizer (by fun_prop) (by fun_prop)
    funext f
    exact congr_fun (core f) v
  exact congr_fun he u

end SobolevChart

end
end

end OAI
