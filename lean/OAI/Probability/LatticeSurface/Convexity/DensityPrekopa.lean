import Mathlib
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.USCEnvelope
import OAI.Probability.LatticeSurface.Convexity.USCGlobal
import OAI.Probability.LatticeSurface.Convexity.USCMarginal
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

end FacetVolume

open Set Filter

open scoped Topology

noncomputable section

namespace Overlap

end Overlap

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end USCEnvelope

namespace FacetVolume

end FacetVolume

namespace FacetVolume

lemma integral_eval_fin_one (f : ℝ → ℝ) : (∫ x : Fin 1 → ℝ,f (x 0))=∫ x,f x := by
  exact (volume_preserving_funUnique (Fin 1) ℝ).integral_comp
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding f

lemma real_usc_prekopa_leindler {a b s t : ℝ} {f g h : ℝ → ℝ}
    (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) (hh : UpperSemicontinuous h)
    (hab : a<b) (hs : 0 < s) (ht : 0 < t) (hst : s+t=1)
    (hf0 : ∀ x,0≤f x) (hg0 : ∀ x,0≤g x) (hh0 : ∀ x,0≤h x)
    (hfK : ∀ x,x∉Icc a b → f x=0) (hgK : ∀ x,x∉Icc a b → g x=0)
    (hhK : ∀ x,x∉Icc a b → h x=0)
    (hcomb : ∀ x y,(f x)^s*(g y)^t≤h (s*x+t*y)) :
    (∫ x,f x)^s*(∫ x,g x)^t≤∫ x,h x := by
  have hsupp (p : ℝ → ℝ) (hp : ∀ x,x∉Icc a b → p x=0) (x : Fin 1 → ℝ)
      (hx : x∉cube 1 a b) : p (x 0)=0 := by
    apply hp
    intro h
    apply hx
    exact mem_cube.mpr (fun i => by have : i=0 := Subsingleton.elim _ _;simpa [this] using h)
  have hPL := global_usc_prekopa_leindler 1
    (hf.comp (continuous_apply 0)) (hg.comp (continuous_apply 0)) (hh.comp (continuous_apply 0))
    hab hs ht hst (fun x => hf0 _) (fun x => hg0 _) (fun x => hh0 _)
    (hsupp f hfK) (hsupp g hgK) (hsupp h hhK) (fun x y => hcomb (x 0) (y 0))
  simpa only [Function.comp_def,integral_eval_fin_one] using hPL

end FacetVolume

namespace Density

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def LogConcave (p : E → ℝ) : Prop :=
  ∀ (x y : E) (s t : ℝ),0 < s → 0 < t → s+t=1 →
    (p x)^s*(p y)^t≤p (s • x+t • y)

end Density

namespace FacetVolume

lemma logConcave_marginal {n : ℕ} {p : (Fin (n+1) → ℝ) → ℝ} {a b : ℝ}
    (hp : UpperSemicontinuous p) (hp0 : ∀ z,0≤p z) (hab : a<b)
    (hpK : ∀ z,z∉cube (n+1) a b → p z=0) (hlc : Density.LogConcave p) :
    Density.LogConcave (fun r => ∫ z : Fin n → ℝ,p (Fin.cons r z)) := by
  intro x y s t hs ht hst
  have hsup (r : ℝ) (z : Fin n → ℝ) (hz : z∉cube n a b) : p (Fin.cons r z)=0 := by
    exact hpK _ (fun h => hz (fin_cons_mem_cube.mp h).2)
  apply global_usc_prekopa_leindler n
    (hp.comp (continuous_const.finCons continuous_id))
    (hp.comp (continuous_const.finCons continuous_id))
    (hp.comp (continuous_const.finCons continuous_id)) hab hs ht hst
    (fun z => hp0 _) (fun z => hp0 _) (fun z => hp0 _)
    (hsup x) (hsup y) (hsup (s*x+t*y))
  intro z w
  have he : s • Fin.cons x z+t • Fin.cons y w=Fin.cons (s*x+t*y) (s • z+t • w) := by
    ext i;refine Fin.cases ?_ (fun j => ?_) i <;> simp
  simpa only [he,Function.comp_def,id_eq] using hlc (Fin.cons x z) (Fin.cons y w) s t hs ht hst

end FacetVolume

end
end
end

end OAI
