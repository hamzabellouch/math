import OAI.Analysis.LipschitzHilbert.Trees.LineSamplingPath
import OAI.Analysis.LipschitzHilbert.Fourier.LineLpDerivative

namespace OAI

/-! Strong L2 derivatives of the actual sampling paths. -/
noncomputable section
open Filter MeasureTheory
open scoped ContDiff Topology
namespace LipschitzHilbert.PacketRepresentation

def lineSchwartzDerivativeBound (f : SchwartzMap ℝ ℂ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (schwartzDerivative 1 f)

theorem lineSchwartzDerivativeBound_nonneg (f : SchwartzMap ℝ ℂ) :
    0≤lineSchwartzDerivativeBound f := apply_nonneg _ _

theorem lineSchwartz_lipschitz (f : SchwartzMap ℝ ℂ) :
    LipschitzWith ⟨lineSchwartzDerivativeBound f,lineSchwartzDerivativeBound_nonneg f⟩ f := by
  apply lipschitzWith_of_nnnorm_deriv_le f.differentiable
  intro x
  change ‖deriv f x‖≤lineSchwartzDerivativeBound f
  exact SchwartzMap.norm_le_seminorm ℝ (schwartzDerivative 1 f) x

theorem line_small_eventually (t : ℝ) (ht : |t|<1/2) : ∀ᶠ s in 𝓝 t, |s|≤1/2 := by
  have hm := abs_lt.mp ht
  filter_upwards [Ioo_mem_nhds hm.1 hm.2] with s hs
  exact abs_le.mpr ⟨hs.1.le,hs.2.le⟩

variable (u : ℝ → ℝ) (hu : LipschitzWith 1 u) (hc : ContDiff ℝ ∞ u)
  (hcompact : HasCompactSupport u) (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B)

theorem lineSamplingPath_L2_hasDerivAt (t : ℝ) (ht : |t|<1/2) (f : SchwartzMap ℝ ℂ) :
    HasDerivAt (fun s => (lineSamplingPath u hu hc hcompact s f).toLp 2 volume)
      ((lineSamplingTangent u hu hc hcompact t ht.le f).toLp 2 volume) t := by
  apply lineLp_hasDerivAt_of_increment_bound
    (fun s => (lineSamplingPath u hu hc hcompact s f : ℝ → ℂ))
    (lineSamplingTangent u hu hc hcompact t ht.le f) t
    (fun s => (lineSamplingPath u hu hc hcompact s f).memLp 2 volume)
    ((lineSamplingTangent u hu hc hcompact t ht.le f).memLp 2 volume)
    (fun y => lineSchwartzDerivativeBound f*|u y|)
  · have hi := ((lineDirectionSchwartz u hc hcompact).memLp 2 volume).integrable_norm_pow
      (by decide : (2:ℕ)≠0)
    simpa only [lineDirectionSchwartz_apply,Complex.norm_real,Real.norm_eq_abs,mul_pow] using
      hi.const_mul (lineSchwartzDerivativeBound f^2)
  · filter_upwards [line_small_eventually t ht] with s hs y
    rw [lineSamplingPath_apply u hu hc hcompact s hs,
      lineSamplingPath_apply u hu hc hcompact t ht.le]
    have hh := (lineSchwartz_lipschitz f).dist_le_mul (lineSampling u s y) (lineSampling u t y)
    simp only [dist_eq_norm,Real.norm_eq_abs] at hh
    calc
      ‖f (lineSampling u s y)-f (lineSampling u t y)‖ ≤
          lineSchwartzDerivativeBound f*|lineSampling u s y-lineSampling u t y| := hh
      _ = |s-t| *(lineSchwartzDerivativeBound f*|u y|) := by
        rw [show lineSampling u s y-lineSampling u t y=(t-s)*u y by simp only [lineSampling]; ring,
          abs_mul,abs_sub_comm t s]
        ring
  · exact lineSamplingPath_hasDerivAt u hu hc hcompact t ht f

theorem lineSamplingInversePath_L2_hasDerivAt (t : ℝ) (ht : |t|<1/2) (f : SchwartzMap ℝ ℂ) :
    HasDerivAt (fun s => (lineSamplingInversePath u hu hc hcompact B hB hb s f).toLp 2 volume)
      ((lineSamplingInverseTangent u hu hc hcompact B hB hb t ht.le f).toLp 2 volume) t := by
  apply lineLp_hasDerivAt_of_increment_bound
    (fun s => (lineSamplingInversePath u hu hc hcompact B hB hb s f : ℝ → ℂ))
    (lineSamplingInverseTangent u hu hc hcompact B hB hb t ht.le f) t
    (fun s => (lineSamplingInversePath u hu hc hcompact B hB hb s f).memLp 2 volume)
    ((lineSamplingInverseTangent u hu hc hcompact B hB hb t ht.le f).memLp 2 volume)
    (fun y => 2*lineSchwartzDerivativeBound f*|u (lineSamplingInverse u t y)|)
  · have hi := ((lineSamplingInverseSchwartz u hu hc hcompact B hB hb t ht.le
      (lineDirectionSchwartz u hc hcompact)).memLp 2 volume).integrable_norm_pow
      (by decide : (2:ℕ)≠0)
    convert hi.const_mul ((2*lineSchwartzDerivativeBound f)^2) using 1
    ext y
    simp only [lineSamplingInverseSchwartz_apply,lineDirectionSchwartz_apply,
      Complex.norm_real,Real.norm_eq_abs]
    ring
  · filter_upwards [line_small_eventually t ht] with s hs y
    rw [lineSamplingInversePath_apply u hu hc hcompact B hB hb s hs,
      lineSamplingInversePath_apply u hu hc hcompact B hB hb t ht.le]
    have hh := (lineSchwartz_lipschitz f).dist_le_mul
      (lineSamplingInverse u s y) (lineSamplingInverse u t y)
    simp only [dist_eq_norm,Real.norm_eq_abs] at hh
    calc
      ‖f (lineSamplingInverse u s y)-f (lineSamplingInverse u t y)‖ ≤
          lineSchwartzDerivativeBound f*|lineSamplingInverse u s y-lineSamplingInverse u t y| := hh
      _ ≤ lineSchwartzDerivativeBound f*(2*|s-t| *|u (lineSamplingInverse u t y)|) :=
        mul_le_mul_of_nonneg_left (lineSamplingInverse_time_pointwise u hu B hB hb s t hs y)
          (lineSchwartzDerivativeBound_nonneg f)
      _ = |s-t| *(2*lineSchwartzDerivativeBound f*|u (lineSamplingInverse u t y)|) := by ring
  · exact lineSamplingInversePath_hasDerivAt u hu hc hcompact B hB hb t ht f

end LipschitzHilbert.PacketRepresentation

end

end OAI
