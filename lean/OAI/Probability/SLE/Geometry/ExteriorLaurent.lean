import OAI.Probability.SLE.Loewner.SlitExteriorChart
import OAI.Probability.SLE.Geometry.SymmetricSlope

namespace OAI

/-! Removing the pole of the exterior slit chart at infinity gives its
first two Laurent coefficients without choosing a power-series expansion. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

def slitInfinityFactor (f : ℂ → ℂ) (a : ℝ) (w : ℂ) : ℂ :=
  (a:ℂ) * ((dslope f 0 w)⁻¹+w^2*dslope f 0 w)

lemma slitInfinityFactor_zero {f : ℂ → ℂ} {a : ℝ}
    (ha : a ≠ 0) (hd : deriv f 0=(a:ℂ)) : slitInfinityFactor f a 0=1 := by
  simp only [slitInfinityFactor,dslope_same,hd,zero_pow two_ne_zero,zero_mul,add_zero]
  exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ha)

lemma slitInfinityFactor_analyticAt {f : ℂ → ℂ} {a : ℝ}
    (hf : AnalyticAt ℂ f 0) (ha : a ≠ 0) (hd : deriv f 0=(a:ℂ)) :
    AnalyticAt ℂ (slitInfinityFactor f a) 0 := by
  have hq := analyticAt_dslope_zero hf
  have hq0 : dslope f 0 0 ≠ 0 := by
    rw [dslope_same,hd]
    exact Complex.ofReal_ne_zero.mpr ha
  exact analyticAt_const.mul ((hq.inv hq0).add ((analyticAt_id.pow 2).mul hq))

lemma slitInfinityFactor_reflection {D : Set ℂ} (hD : D ∈ 𝓝 (0:ℂ))
    {f : ℂ → ℂ} (hs : ∀ z ∈ D, f (conj z)=conj (f z)) (a : ℝ) :
    ∀ z ∈ D, slitInfinityFactor f a (conj z)=conj (slitInfinityFactor f a z) := by
  intro z hz
  simp only [slitInfinityFactor,dslope_reflection hD hs z hz,map_mul,map_add,map_inv₀,
    map_pow,conj_ofReal]

lemma slitInfinityFactor_identity {f : ℂ → ℂ} (hf0 : f 0=0) (a : ℝ)
    {z : ℂ} (hz : z ≠ 0) :
    z*slitInfinityFactor f a z⁻¹=(a:ℂ)*exteriorJoukowski (slitExteriorMap f z) := by
  have hq : dslope f 0 z⁻¹=z*f z⁻¹ := by
    simp only [dslope_of_ne _ (inv_ne_zero hz),slope,vsub_eq_sub,sub_zero,hf0,inv_inv,smul_eq_mul]
  simp only [slitInfinityFactor,hq,exteriorJoukowski,slitExteriorMap,inv_inv,mul_inv_rev]
  field_simp

lemma slitInfinityFactor_remainder {f : ℂ → ℂ} {a : ℝ}
    (hf0 : f 0=0) (ha : a ≠ 0) (hd : deriv f 0=(a:ℂ)) {z : ℂ} (hz : z ≠ 0) :
    z*((a:ℂ)*exteriorJoukowski (slitExteriorMap f z)-
        deriv (slitInfinityFactor f a) 0-z)=
      dslope (dslope (slitInfinityFactor f a) 0) 0 z⁻¹ := by
  have h0 := slitInfinityFactor_zero ha hd
  have h1 := sub_smul_dslope (slitInfinityFactor f a) (0:ℂ) z⁻¹
  have h2 := sub_smul_dslope (dslope (slitInfinityFactor f a) 0) (0:ℂ) z⁻¹
  simp only [sub_zero,smul_eq_mul,dslope_same,h0] at h1 h2
  have hmul : (a:ℂ)*exteriorJoukowski (slitExteriorMap f z)=
      z*slitInfinityFactor f a z⁻¹ := (slitInfinityFactor_identity hf0 a hz).symm
  rw [hmul]
  have hz1 : z*z⁻¹=1 := mul_inv_cancel₀ hz
  calc
    z*(z*slitInfinityFactor f a z⁻¹-deriv (slitInfinityFactor f a) 0-z) =
      z*(z*(z⁻¹*dslope (slitInfinityFactor f a) 0 z⁻¹+1)-
        deriv (slitInfinityFactor f a) 0-z) := by rw [h1]; ring
    _ = z*(dslope (slitInfinityFactor f a) 0 z⁻¹-deriv (slitInfinityFactor f a) 0) := by
      rw [mul_add,← mul_assoc,hz1,one_mul,mul_one]
      ring
    _ = z*(z⁻¹*dslope (dslope (slitInfinityFactor f a) 0) 0 z⁻¹) := by rw [h2]
    _ = _ := by rw [← mul_assoc,hz1,one_mul]

lemma slitExteriorMap_laurent_limit {f : ℂ → ℂ} {a : ℝ}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0) (ha : a ≠ 0)
    (hd : deriv f 0=(a:ℂ)) :
    Tendsto (fun z : ℂ => z*((a:ℂ)*exteriorJoukowski (slitExteriorMap f z)-
        deriv (slitInfinityFactor f a) 0-z)) (cocompact ℂ)
      (𝓝 (deriv (dslope (slitInfinityFactor f a) 0) 0)) := by
  have hH := slitInfinityFactor_analyticAt hf ha hd
  have hq := analyticAt_dslope_zero hH
  have hr := analyticAt_dslope_zero hq
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0))
  have ht := hr.continuousAt.tendsto.comp hinv
  simp only [dslope_same] at ht
  apply ht.congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  exact (slitInfinityFactor_remainder hf0 ha hd hz).symm

end SLEExactGauge

end

end OAI
