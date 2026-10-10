import Mathlib
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.DensityPrekopa
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

end FacetVolume

namespace Density

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Density

namespace FacetVolume

end FacetVolume

namespace Density

lemma even_abs {p : ℝ → ℝ} (heven : ∀ x,p (-x)=p x) (x : ℝ) : p |x|=p x := by
  rcases le_total 0 x with hx|hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx,heven]

lemma antitone_nonneg_of_even_logConcave {p : ℝ → ℝ} (hp0 : ∀ x,0≤p x)
    (heven : ∀ x,p (-x)=p x) (hlc : LogConcave p) : AntitoneOn p (Ici 0) := by
  intro x hx y hy hxy
  by_cases heq : x=y
  · simp [heq]
  have hypos : 0<y := lt_of_le_of_lt hx (lt_of_le_of_ne hxy heq)
  by_cases hpy : p y=0
  · rw [hpy];exact hp0 x
  have hyp : 0<p y := (hp0 y).lt_of_ne' hpy
  let s : ℝ := (y-x)/(2*y)
  let t : ℝ := (y+x)/(2*y)
  have hs : 0 < s := div_pos (sub_pos.mpr (lt_of_le_of_ne hxy heq)) (by positivity)
  have ht : 0 < t := div_pos (add_pos_of_pos_of_nonneg hypos hx) (by positivity)
  have hst : s+t=1 := by dsimp [s,t];field_simp;ring
  have he : s • (-y)+t • y=x := by dsimp [s,t];field_simp;ring
  have h := hlc (-y) y s t hs ht hst
  rw [he,heven,← Real.rpow_add hyp,hst,Real.rpow_one] at h
  exact h

lemma even_logConcave_shift {p : ℝ → ℝ} (hp0 : ∀ x,0≤p x)
    (heven : ∀ x,p (-x)=p x) (hlc : LogConcave p) {r T : ℝ} (hr : 0≤r) (hT : 0≤T) :
    p (r+T)≤Real.sqrt (p (r-T)*p (r+T)) := by
  have habs : |r-T|≤r+T := abs_le.mpr ⟨by linarith,by linarith⟩
  have hp := antitone_nonneg_of_even_logConcave hp0 heven hlc
    (abs_nonneg (r-T)) (add_nonneg hr hT) habs
  rw [even_abs heven] at hp
  apply (Real.le_sqrt (hp0 _) (mul_nonneg (hp0 _) (hp0 _))).2
  nlinarith [mul_le_mul_of_nonneg_right hp (hp0 (r+T))]

end Density

end
end
end

end OAI
