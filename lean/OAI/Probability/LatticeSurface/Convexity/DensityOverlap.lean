import Mathlib
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.DensityPrekopa
import OAI.Probability.LatticeSurface.Convexity.EvenIntegral
import OAI.Probability.LatticeSurface.Convexity.MarginalOverlap
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.Survival
import OAI.Probability.LatticeSurface.Convexity.USCEnvelope
import OAI.Probability.LatticeSurface.Convexity.USCGlobal
import OAI.Probability.LatticeSurface.Convexity.USCMarginal
import OAI.Probability.LatticeSurface.Convexity.USCPrekopa
import OAI.Probability.LatticeSurface.Convexity.USCProduct
import OAI.Probability.LatticeSurface.Convexity.Unimodal
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.CompactOverlap
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

end FacetVolume

namespace Density

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Density

namespace FacetVolume

end FacetVolume

namespace Overlap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

end Overlap

namespace FacetVolume

end FacetVolume

namespace Density

open FacetVolume

end Density

namespace Density

end Density

namespace Density

end Density

namespace Density

lemma midpoint_support {p : ℝ → ℝ} {R : ℝ}
    (hpK : ∀ x,x∉Icc (-R) R → p x=0) (T r : ℝ) (hr : r∉Icc (-R) R) :
    Real.sqrt (p (r-T)*p (r+T))=0 := by
  by_cases hminus : p (r-T)=0
  · simp [hminus]
  by_cases hplus : p (r+T)=0
  · simp [hplus]
  have hm : r-T∈Icc (-R) R := by by_contra h;exact hminus (hpK _ h)
  have hp : r+T∈Icc (-R) R := by by_contra h;exact hplus (hpK _ h)
  exfalso
  apply hr
  constructor <;> linarith [hm.1,hm.2,hp.1,hp.2]

lemma overlap_survival_bound {p : ℝ → ℝ} {R T : ℝ}
    (hT : 0≤T) (hp : UpperSemicontinuous p) (hp0 : ∀ x,0≤p x)
    (hpK : ∀ x,x∉Icc (-R) R → p x=0) (heven : ∀ x,p (-x)=p x)
    (hlc : LogConcave p) :
    2*(∫ x in Ici T,p x)≤∫ x,Real.sqrt (p (x-T)*p (x+T)) := by
  let B : ℝ → ℝ := fun r => Real.sqrt (p (r-T)*p (r+T))
  have hu : UpperSemicontinuous B := Overlap.usc_sqrt
    (Overlap.usc_mul (hp.comp (continuous_id.sub continuous_const))
      (hp.comp (continuous_id.add continuous_const)) (fun x => hp0 _) (fun x => hp0 _))
  have hi : Integrable B := integrable_real_usc hu (fun x => Real.sqrt_nonneg _) (midpoint_support hpK T)
  have hpi : Integrable p := integrable_real_usc hp hp0 hpK
  have hshift : Integrable (fun x => p (x+T)) :=
    (measurePreserving_add_right (volume : Measure ℝ) T).integrable_comp_emb
      (Homeomorph.addRight T).measurableEmbedding |>.mpr hpi
  have he : ∀ x,B (-x)=B x := by
    intro x
    have h1 : -x-T= -(x+T) := by ring
    have h2 : -x+T= -(x-T) := by ring
    simp only [B,h1,h2,heven,mul_comm]
  rw [even_integral hi he]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [← integral_shift_Ici p T]
  apply setIntegral_mono_on hshift.integrableOn hi.integrableOn measurableSet_Ici
  intro x hx
  exact even_logConcave_shift hp0 heven hlc hx hT

end Density

namespace FacetVolume

lemma integral_coordinate_set {n : ℕ} {p : (Fin (n+1) → ℝ) → ℝ} (hp : Integrable p)
    {S : Set ℝ} (hS : MeasurableSet S) :
    (∫ x in {x | x 0∈S},p x)=∫ r in S,∫ z : Fin n → ℝ,p (Fin.cons r z) := by
  have hs : MeasurableSet {x : Fin (n+1) → ℝ | x 0∈S} := hS.preimage (measurable_pi_apply 0)
  rw [← integral_indicator hs,← integral_indicator hS,integral_fin_cons (hp.indicator hs)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro r
  by_cases hr : r∈S
  · simp only [Set.indicator_of_mem hr]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => Set.indicator_of_mem (by simpa) p)
  · simp only [Set.indicator_of_notMem hr]
    have hz (z : Fin n → ℝ) : ({x : Fin (n+1) → ℝ | x 0∈S}).indicator p (Fin.cons r z)=0 :=
      Set.indicator_of_notMem (by simpa) p
    simp_rw [hz];simp

end FacetVolume

end
end
end

end OAI
