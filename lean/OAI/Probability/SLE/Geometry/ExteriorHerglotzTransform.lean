import OAI.Probability.SLE.Loewner.ReflectedExteriorAnalytic
import Mathlib.Analysis.Complex.RemovableSingularity

namespace OAI

/-! Inversion converts the vanishing exterior hydrodynamic displacement
into a disk function whose value at zero is exactly capacity/radius. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

def exteriorHerglotzRaw (G : ℂ → ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  (1-w^2)/w*(G ((R:ℂ)/w)-(R:ℂ)/w)

noncomputable def exteriorHerglotzTransform (G : ℂ → ℂ) (R c : ℝ) : ℂ → ℂ :=
  Function.update (exteriorHerglotzRaw G R) 0 ((c:ℂ)/(R:ℂ))

@[simp] lemma exteriorHerglotzTransform_zero (G : ℂ → ℂ) (R c : ℝ) :
    exteriorHerglotzTransform G R c 0=(c:ℂ)/(R:ℂ) := Function.update_self _ _ _

lemma exteriorHerglotzRaw_identity (G : ℂ → ℂ) {R : ℝ} (hR : R≠0)
    {w : ℂ} (hw : w≠0) :
    exteriorHerglotzRaw G R w=(1-w^2)/(R:ℂ)*
      (((R:ℂ)/w)*(G ((R:ℂ)/w)-(R:ℂ)/w)) := by
  unfold exteriorHerglotzRaw
  field_simp [ofReal_ne_zero.mpr hR,hw]

lemma scaled_inverse_tendsto_cocompact {R : ℝ} (hR : R≠0) :
    Tendsto (fun w : ℂ => (R:ℂ)/w) (𝓝[≠] (0:ℂ)) (cocompact ℂ) := by
  have hi : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] (0:ℂ)) (cocompact ℂ) := by
    simpa only [Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_nhdsNE_zero : Tendsto (Inv.inv : ℂ → ℂ) (𝓝[≠] (0:ℂ)) (Bornology.cobounded ℂ))
  have hh :=
    (Homeomorph.mulLeft₀ (R:ℂ) (ofReal_ne_zero.mpr hR)).isClosedEmbedding.tendsto_cocompact.comp hi
  change Tendsto (fun w : ℂ => (R:ℂ)*w⁻¹) (𝓝[≠] (0:ℂ)) (cocompact ℂ) at hh
  simpa only [div_eq_mul_inv] using hh

theorem exteriorHerglotzTransform_continuousAt_zero {G : ℂ → ℂ} {R c : ℝ} (hR : R≠0)
    (hc : Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ) (𝓝 (c:ℂ))) :
    ContinuousAt (exteriorHerglotzTransform G R c) 0 := by
  apply continuousAt_update_same.mpr
  have hsmall : Tendsto (fun w : ℂ => (1-w^2)/(R:ℂ)) (𝓝[≠] (0:ℂ)) (𝓝 (1/(R:ℂ))) := by
    have hh : Continuous (fun w : ℂ => (1-w^2)/(R:ℂ)) :=
      (continuous_const.sub (continuous_id.pow 2)).div_const _
    have ht := (hh.tendsto 0).mono_left (show 𝓝[≠] (0:ℂ)≤𝓝 (0:ℂ) from inf_le_left)
    simpa only [zero_pow two_ne_zero,sub_zero] using ht
  have ht := hsmall.mul (hc.comp (scaled_inverse_tendsto_cocompact hR))
  have he : (1/(R:ℂ))*(c:ℂ)=(c:ℂ)/(R:ℂ) := by ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact (exteriorHerglotzRaw_identity G hR hw).symm

end SLEExactGauge

end

end OAI
