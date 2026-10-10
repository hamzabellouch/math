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

open FacetVolume

lemma integrable_real_usc {p : ℝ → ℝ} {a b : ℝ}
    (hp : UpperSemicontinuous p) (hp0 : ∀ x,0≤p x)
    (hpK : ∀ x,x∉Icc a b → p x=0) : Integrable p := by
  have hi : Integrable (fun z : Fin 1 → ℝ => p (z 0)) := by
    apply integrable_usc_compact (a:=a) (b:=b) (hp.comp (continuous_apply 0)) (fun z => hp0 _)
    intro z hz
    apply hpK
    intro h
    apply hz
    exact mem_cube.mpr (fun i => by have : i=0 := Subsingleton.elim _ _;simpa [this] using h)
  exact (volume_preserving_funUnique (Fin 1) ℝ).integrable_comp_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding |>.mp hi

lemma logConcave_survival {p : ℝ → ℝ} {a b : ℝ}
    (hp : UpperSemicontinuous p) (hp0 : ∀ x,0≤p x) (hab : a<b)
    (hpK : ∀ x,x∉Icc a b → p x=0) (hlc : LogConcave p) :
    LogConcave (fun r => ∫ x in Ici r,p x) := by
  intro r v s t hs ht hst
  let f : ℝ → ℝ → ℝ := fun r => (Ici r).indicator p
  have hfu (r : ℝ) : UpperSemicontinuous (f r) := Overlap.usc_indicator hp hp0 isClosed_Ici
  have hfp (r x : ℝ) : 0≤f r x := Set.indicator_nonneg (fun x _ => hp0 x) x
  have hfK (r x : ℝ) (hx : x∉Icc a b) : f r x=0 := by simp [f,hpK x hx]
  have h := real_usc_prekopa_leindler (hfu r) (hfu v) (hfu (s*r+t*v)) hab hs ht hst
    (hfp r) (hfp v) (hfp (s*r+t*v)) (hfK r) (hfK v) (hfK (s*r+t*v)) ?_
  · simpa only [f,integral_indicator measurableSet_Ici,smul_eq_mul] using h
  · intro x y
    by_cases hx : r≤x
    · by_cases hy : v≤y
      · have hxy : s*r+t*v≤ s*x+t*y := add_le_add (mul_le_mul_of_nonneg_left hx hs.le) (mul_le_mul_of_nonneg_left hy ht.le)
        simpa [f,hx,hy,hxy,smul_eq_mul] using hlc x y s t hs ht hst
      · have hy' : y∉Ici v := hy
        simp only [f,Set.indicator_of_notMem hy',Real.zero_rpow ht.ne',mul_zero]
        exact hfp _ _
    · have hx' : x∉Ici r := hx
      simp only [f,Set.indicator_of_notMem hx',Real.zero_rpow hs.ne',zero_mul]
      exact hfp _ _

lemma logConcave_const_mul {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : E → ℝ} (hp0 : ∀ x,0≤p x) (hp : LogConcave p) {c : ℝ} (hc : 0<c) :
    LogConcave (fun x => c*p x) := by
  intro x y s t hs ht hst
  rw [Real.mul_rpow hc.le (hp0 x),Real.mul_rpow hc.le (hp0 y)]
  calc
    _ = (c^s*c^t)*(p x^s*p y^t) := by ring
    _ = c*(p x^s*p y^t) := by rw [← Real.rpow_add hc,hst,Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hp x y s t hs ht hst) hc.le

lemma geometric_tail {H : ℝ → ℝ} (hH0 : ∀ x,0≤H x) (hH : LogConcave H)
    (hzero : H 0=1) {T q : ℝ} (_hq0 : 0≤q) (hT : H T≤q) (j : ℕ) :
    H (j*T)≤q^j := by
  rcases j with _|j
  · simp [hzero]
  rcases j with _|j
  · simpa using hT
  have hj : (0:ℝ)<j+2 := by positivity
  have hjne : (j+2:ℝ)≠0 := ne_of_gt hj
  have hinv : 0 < (j+2:ℝ)⁻¹ := inv_pos.mpr hj
  have hrem : 0 < 1-(j+2:ℝ)⁻¹ := by rw [sub_pos,inv_lt_one₀ hj];linarith [Nat.cast_nonneg (α:=ℝ) j]
  have hl := hH ((j+2)*T) 0 ((j+2:ℝ)⁻¹) (1-(j+2:ℝ)⁻¹) hinv hrem (by ring)
  have he : (j+2:ℝ)⁻¹ • ((j+2)*T)+(1-(j+2:ℝ)⁻¹) • 0=T := by
    simp only [smul_eq_mul,mul_zero,add_zero];field_simp
  rw [he,hzero,Real.one_rpow,mul_one] at hl
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg (hH0 _) _) (hl.trans hT) (j+2)
  rw [show (j+2:ℝ)⁻¹=((j+2:ℕ):ℝ)⁻¹ by norm_num,Real.rpow_inv_natCast_pow (hH0 _) (by omega)] at hh
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.succ_eq_add_one,add_assoc,show (1:ℝ)+1=2 by norm_num,show 1+1=2 by norm_num] using hh

end Density

end
end
end

end OAI
