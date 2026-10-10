import OAI.Analysis.LipschitzHilbert.Fourier.LineSamplingSchwartz

namespace OAI

/-! Total Schwartz paths for short-time sampling. Outside the interval
needed in the proof the paths are extended by the identity. -/
noncomputable section
open Filter MeasureTheory
open scoped ContDiff Topology
namespace LipschitzHilbert.PacketRepresentation

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u) (hc : ContDiff ℝ ∞ u)
  (hcompact : HasCompactSupport u) (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

def lineDirectionSchwartz : SchwartzMap ℝ ℂ :=
  (hcompact.toSchwartzMap hc).postcompCLM Complex.ofRealCLM

@[simp] theorem lineDirectionSchwartz_apply (y : ℝ) :
    lineDirectionSchwartz u hc hcompact y=(u y:ℂ) := rfl

def lineSamplingPath (s : ℝ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  if hs : |s|≤1/2 then lineSamplingSchwartz u hu hc hcompact s hs f else f

def lineSamplingInversePath (s : ℝ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  if hs : |s|≤1/2 then lineSamplingInverseSchwartz u hu hc hcompact B hB hb s hs f else f

theorem lineSamplingPath_apply (s : ℝ) (hs : |s|≤1/2) (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    lineSamplingPath u hu hc hcompact s f y=f (lineSampling u s y) := by
  simp only [lineSamplingPath,dite_eq_left hs,lineSamplingSchwartz_apply]

theorem lineSamplingInversePath_apply (s : ℝ) (hs : |s|≤1/2) (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    lineSamplingInversePath u hu hc hcompact B hB hb s f y=f (lineSamplingInverse u s y) := by
  simp only [lineSamplingInversePath,dite_eq_left hs,lineSamplingInverseSchwartz_apply]

def lineSamplingTangent (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  -lineSchwartzProduct (lineDirectionSchwartz u hc hcompact)
    (lineSamplingSchwartz u hu hc hcompact t ht (schwartzDerivative 1 f))

def lineSamplingInverseTangent (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  -lineSchwartzProduct (lineSamplingGeneratorSchwartz u hu hc hcompact B hB hb t ht)
    (schwartzDerivative 1 (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f))

theorem lineSamplingTangent_apply (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    lineSamplingTangent u hu hc hcompact t ht f y=
      (-u y) • deriv f (lineSampling u t y) := by
  simp only [lineSamplingTangent,neg_apply,lineSchwartzProduct_apply,lineDirectionSchwartz_apply,
    lineSamplingSchwartz_apply,schwartzDerivative_one_apply,neg_smul,Complex.real_smul]

theorem lineSamplingInverseTangent_apply (t : ℝ) (ht : |t|≤1/2) (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    lineSamplingInverseTangent u hu hc hcompact B hB hb t ht f y=
      (u (lineSamplingInverse u t y)/(1-t*deriv u (lineSamplingInverse u t y))) •
        deriv f (lineSamplingInverse u t y) := by
  have hdu := (hc.differentiable (by simp)) (lineSamplingInverse u t y)
  have hd := (f.differentiable _).hasDerivAt.scomp y
    (lineSamplingInverse_space_hasDerivAt u hu B hB hb t ht y hdu)
  have hid : deriv (lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht f) y=
      (1-t*deriv u (lineSamplingInverse u t y))⁻¹ • deriv f (lineSamplingInverse u t y) := hd.deriv
  simp only [lineSamplingInverseTangent,neg_apply,lineSchwartzProduct_apply,
    schwartzDerivative_one_apply,lineSamplingGeneratorSchwartz_apply,lineSamplingGenerator]
  rw [hid,←lineSamplingInverse_eq u hu B hB hb t ht]
  simp only [Complex.ofReal_neg,neg_mul,neg_neg,←Complex.real_smul,smul_smul,div_eq_mul_inv]

theorem lineSamplingPath_hasDerivAt (t : ℝ) (ht : |t|<1/2) (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    HasDerivAt (fun s => lineSamplingPath u hu hc hcompact s f y)
      (lineSamplingTangent u hu hc hcompact t ht.le f y) t := by
  have hi : HasDerivAt (fun s : ℝ => lineSampling u s y) (-u y) t := by
    convert (hasDerivAt_const t y).sub ((hasDerivAt_id t).mul_const (u y)) using 1 <;> simp [lineSampling]
    rfl
  have hd := (f.differentiable _).hasDerivAt.scomp t hi
  rw [←lineSamplingTangent_apply u hu hc hcompact t ht.le f y] at hd
  apply hd.congr_of_eventuallyEq
  have hm := abs_lt.mp ht
  filter_upwards [Ioo_mem_nhds hm.1 hm.2] with s hs
  exact lineSamplingPath_apply u hu hc hcompact s (abs_le.mpr ⟨hs.1.le,hs.2.le⟩) f y

theorem lineSamplingInversePath_hasDerivAt (t : ℝ) (ht : |t|<1/2) (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    HasDerivAt (fun s => lineSamplingInversePath u hu hc hcompact B hB hb s f y)
      (lineSamplingInverseTangent u hu hc hcompact B hB hb t ht.le f y) t := by
  have hi := lineSamplingInverse_time_hasDerivAt u hu B hB hb t ht y
    ((hc.differentiable (by simp)) _)
  have hd := (f.differentiable _).hasDerivAt.scomp t hi
  rw [←lineSamplingInverseTangent_apply u hu hc hcompact B hB hb t ht.le f y] at hd
  apply hd.congr_of_eventuallyEq
  have hm := abs_lt.mp ht
  filter_upwards [Ioo_mem_nhds hm.1 hm.2] with s hs
  exact lineSamplingInversePath_apply u hu hc hcompact B hB hb s
    (abs_le.mpr ⟨hs.1.le,hs.2.le⟩) f y

end LipschitzHilbert.PacketRepresentation

end

end OAI
