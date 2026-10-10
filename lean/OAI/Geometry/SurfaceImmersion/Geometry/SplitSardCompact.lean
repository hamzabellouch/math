import OAI.Geometry.SurfaceImmersion.Geometry.SliceDerivativeSurjective
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! Fiberwise Sard nullity gives null critical images for split maps,
first on compact sets so measurability follows directly from continuity. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasureSpace F] [BorelSpace F] [SFinite (volume : Measure F)]

theorem split_sard_compact
    (hsard : ∀ (g : E → F) (V : Set E), IsOpen V → ContDiffOn ℝ ∞ g V →
      volume (g '' {x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g x)}) = 0)
    {f : (ℝ × E) → ℝ × F} {U K : Set (ℝ × E)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hfirst : ∀ z ∈ U, (f z).1 = z.1)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hcrit : ∀ z ∈ K, ¬ Function.Surjective (fderiv ℝ f z)) :
    volume (f '' K) = 0 := by
  have him : IsCompact (f '' K) := hK.image_of_continuousOn (hf.continuousOn.mono hKU)
  apply Measure.measure_prod_null_of_ae_null him.measurableSet
  filter_upwards [] with a
  let g : E → F := fun x => (f (a,x)).2
  let V : Set E := {x | (a,x) ∈ U}
  have hV : IsOpen V := hU.preimage (continuous_const.prodMk continuous_id)
  have hg : ContDiffOn ℝ ∞ g V :=
    (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hx => hx)).snd
  apply measure_mono_null _ (hsard g V hV hg)
  rintro y ⟨z,hz,heq⟩
  have ha : z.1 = a := (hfirst z (hKU hz)).symm.trans (congrArg Prod.fst heq)
  have hz' : z = (a,z.2) := by ext <;> simp [ha]
  refine ⟨z.2,⟨?_,?_⟩,?_⟩
  · change (a,z.2) ∈ U
    rw [← hz']
    exact hKU hz
  · apply slice_derivative_not_surjective hU hf hfirst a z.2
    · rw [← hz']; exact hKU hz
    · rw [← hz']; exact hcrit z hz
  · change (f (a,z.2)).2 = y
    rw [← hz']
    exact congrArg Prod.snd heq

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
