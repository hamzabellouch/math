import OAI.Analysis.LipschitzHilbert.Fourier.LineSamplingInverse

namespace OAI

/-! Differentiation in time of the actual inverse sampling map. -/
noncomputable section
open Filter Set
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem lineSampling_deriv_ne_zero (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (t : ℝ) (ht : |t|≤1/2) (x : ℝ) : 1-t*deriv u x≠0 := by
  have hd : |deriv u x|≤1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz (x₀:=x) hu
  have hp : |t*deriv u x|≤1/2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hd (abs_nonneg t)).trans (by simpa only [mul_one] using ht)
  have hh := (abs_le.mp hp).2
  linarith

theorem lineSamplingInverse_space_hasDerivAt (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) (y : ℝ)
    (hd : DifferentiableAt ℝ u (lineSamplingInverse u t y)) :
    HasDerivAt (lineSamplingInverse u t) (1-t*deriv u (lineSamplingInverse u t y))⁻¹ y := by
  have hf : HasDerivAt (lineSampling u t) (1-t*deriv u (lineSamplingInverse u t y))
      (lineSamplingInverse u t y) := (hasDerivAt_id _).sub (hd.hasDerivAt.const_mul t)
  exact hf.of_local_left_inverse
    (lineSamplingInverse_space_lipschitz u hu B hB hb t ht).continuous.continuousAt
    (lineSampling_deriv_ne_zero u hu t ht _) (Eventually.of_forall
      (lineSampling_inverse_apply u hu B hB hb t))

theorem lineSamplingInverse_time_continuousAt (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|<1/2) (y : ℝ) :
    ContinuousAt (fun s => lineSamplingInverse u s y) t := by
  have hlip : LipschitzOnWith ⟨2*B,by positivity⟩ (fun s => lineSamplingInverse u s y)
      (Icc (-(1/2:ℝ)) (1/2)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs r _hr
    change |lineSamplingInverse u s y-lineSamplingInverse u r y|≤(2*B)*|s-r|
    exact lineSamplingInverse_time_lipschitz u hu B hB hb s r (abs_le.mpr hs) y
  have hm := abs_lt.mp ht
  exact (hlip.continuousOn t ⟨hm.1.le,hm.2.le⟩).continuousAt (Icc_mem_nhds hm.1 hm.2)

theorem lineSamplingInverse_time_hasDerivAt (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|<1/2) (y : ℝ)
    (hdu : DifferentiableAt ℝ u (lineSamplingInverse u t y)) :
    HasDerivAt (fun s => lineSamplingInverse u s y)
      (u (lineSamplingInverse u t y)/(1-t*deriv u (lineSamplingInverse u t y))) t := by
  let g := fun s => lineSamplingInverse u s y
  let x := g t
  have hc : ContinuousAt g t := lineSamplingInverse_time_continuousAt u hu B hB hb t ht y
  have hsmall : ∀ᶠ s in 𝓝 t, |s|≤1/2 := by
    have hm := abs_lt.mp ht
    filter_upwards [Ioo_mem_nhds hm.1 hm.2] with s hs
    exact abs_le.mpr ⟨hs.1.le,hs.2.le⟩
  have heq (s : ℝ) : g s-s*u (g s)=y := lineSampling_inverse_apply u hu B hB hb s y
  by_cases hz : u x=0
  · have hx : x=y := by have hh := heq t; change x-t*u x=y at hh; simpa only [hz,mul_zero,sub_zero] using hh
    have huy : u y=0 := by rwa [hx] at hz
    have hg : g =ᶠ[𝓝 t] fun _ => y := by
      filter_upwards [hsmall] with s hs
      have ha := (lineSampling_antilipschitz u hu s hs).injective
      apply ha
      change g s-s*u (g s)=y-s*u y
      rw [heq s,huy,mul_zero,sub_zero]
    have hd := (hasDerivAt_const t y).congr_of_eventuallyEq hg
    change HasDerivAt g (u x/(1-t*deriv u x)) t
    rw [hz,zero_div]
    exact hd
  · have hun : ∀ᶠ s in 𝓝 t, u (g s)≠0 :=
      (hu.continuous.continuousAt.comp hc).tendsto.eventually (eventually_ne_nhds hz)
    have hden : 1-t*deriv u x≠0 := by
      have hd : |deriv u x|≤1 := by
        simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz (x₀:=x) hu
      have hp : |t*deriv u x|<1/2 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left hd (abs_nonneg t)).trans_lt (by simpa only [mul_one] using ht)
      have hh := (abs_lt.mp hp).2
      linarith
    have hx : x-y=t*u x := by have hh := heq t; change x-t*u x=y at hh; linarith
    have hf : HasDerivAt (fun z => (z-y)/u z) ((1-t*deriv u x)/u x) x := by
      have hnumerator : HasDerivAt (fun z : ℝ => z-y) (1:ℝ) x := (hasDerivAt_id x).sub_const y
      have hdenominator : HasDerivAt u (deriv u x) x := hdu.hasDerivAt
      have hh := hnumerator.div hdenominator hz
      convert hh using 1
      simp only [one_mul]
      rw [hx]
      field_simp [hz]
    have hinv : ∀ᶠ s in 𝓝 t, ((g s-y)/u (g s))=s := by
      filter_upwards [hun] with s hs
      apply (div_eq_iff hs).mpr
      have hh := heq s
      linarith
    have hd := hf.of_local_left_inverse hc (div_ne_zero hden hz) hinv
    simpa only [inv_div] using hd

end LipschitzHilbert.PacketRepresentation

end

end OAI
