import Mathlib
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.USCEnvelope
import OAI.Probability.LatticeSurface.Convexity.USCPrekopa
import OAI.Probability.LatticeSurface.Convexity.USCProduct
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end USCEnvelope

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace FacetVolume

lemma integral_eq_cubeIntegral {n : ℕ} {f : (Fin n → ℝ) → ℝ} {a b : ℝ}
    (hf : ∀ x,x∉cube n a b → f x=0) : (∫ x,f x)=cubeIntegral f a b :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm

lemma global_usc_prekopa_leindler (n : ℕ) {a b s t : ℝ}
    {f g h : (Fin n → ℝ) → ℝ}
    (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) (hh : UpperSemicontinuous h)
    (hab : a<b) (hs : 0 < s) (ht : 0 < t) (hst : s+t=1)
    (hf0 : ∀ x,0≤f x) (hg0 : ∀ x,0≤g x) (hh0 : ∀ x,0≤h x)
    (hfK : ∀ x,x∉cube n a b → f x=0) (hgK : ∀ x,x∉cube n a b → g x=0)
    (hhK : ∀ x,x∉cube n a b → h x=0)
    (hcomb : ∀ x y,(f x)^s*(g y)^t≤h (s • x+t • y)) :
    (∫ x,f x)^s*(∫ x,g x)^t≤∫ x,h x := by
  rw [integral_eq_cubeIntegral hfK,integral_eq_cubeIntegral hgK,integral_eq_cubeIntegral hhK]
  exact compact_usc_prekopa_leindler n hf hg hh hab hs ht hst
    (fun x _ => hf0 x) (fun x _ => hg0 x) (fun x _ => hh0 x) (fun x _ y _ => hcomb x y)

lemma integrable_usc_compact {n : ℕ} {f : (Fin n → ℝ) → ℝ} {a b : ℝ}
    (hf : UpperSemicontinuous f) (hf0 : ∀ x,0≤f x)
    (hfK : ∀ x,x∉cube n a b → f x=0) : Integrable f := by
  have hK := compact_cube n a b
  obtain ⟨M,hM⟩ := (hf.upperSemicontinuousOn _).bddAbove_of_isCompact hK
  have hbound : IntegrableOn (fun _ : Fin n → ℝ => max 0 M) (cube n a b) :=
    continuous_const.continuousOn.integrableOn_compact hK
  have hi : IntegrableOn f (cube n a b) := hbound.mono'
    hf.measurable.aestronglyMeasurable ((ae_restrict_mem (measurable_cube _ _ _)).mono fun x hx => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hf0 x)]
      exact (hM (mem_image_of_mem f hx)).trans (le_max_right _ _))
  have he : (cube n a b).indicator f=f := by
    funext x
    by_cases hx : x∈cube n a b
    · simp [hx]
    · simp [hx,hfK x hx]
  rw [← he]
  exact hi.integrable_indicator (measurable_cube _ _ _)

end FacetVolume

open Set Filter

open scoped Topology

noncomputable section

namespace Overlap

end Overlap

end
end
end

end OAI
