import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarFrameBound

namespace OAI

/-! The actual transverse Gaussian defines a contraction on the full L2
product space. No compact-support or smoothness hypothesis is imposed here. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem line_pair_sq_le (f g : ℝ → ℝ) (hf : MemLp f 2) (hg : MemLp g 2) :
    (∫ z, f z*g z)^2 ≤ (∫ z, f z^2)*(∫ z, g z^2) := by
  have hp (a b : ℝ → ℝ) (ha : MemLp a 2) (hb : MemLp b 2) :
      inner ℝ (ha.toLp a) (hb.toLp b) = ∫ z, a z*b z := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp,hb.coeFn_toLp] with z hz hz'
    rw [hz,hz',RCLike.inner_apply,conj_trivial]
    ring
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [hp f g hf hg,hp f f hf hf,hp g g hg hg] at h
  simpa only [pow_two] using h

def verticalCoefficient (freq : ℝ) (f : SplitPosition → ℝ) (r : PlanarPosition) : ℝ :=
  ∫ z, f (r,z)*verticalMode freq z

theorem split_memLp_vertical_slices (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    ∀ᵐ r : PlanarPosition, MemLp (fun z : ℝ => f (r,z)) 2 := by
  have hp : MemLp f 2 ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    simpa only [Measure.volume_eq_prod] using hf
  filter_upwards [hp.aestronglyMeasurable.prodMk_left,hp.integrable_sq.prod_right_ae] with r hr hi
  exact (memLp_two_iff_integrable_sq hr).mpr hi

/-- The normalized Gaussian coefficient is an L2 contraction on arbitrary
real wavefunctions, including the closure needed for the continuum form. -/
theorem verticalCoefficient_contraction {freq : ℝ} (hfreq : 0 < freq)
    (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    MemLp (verticalCoefficient freq f) 2 ∧
      (∫ r, (verticalCoefficient freq f r)^2) ≤ ∫ p, f p^2 := by
  have hfprod : MemLp f 2 ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    simpa only [Measure.volume_eq_prod] using hf
  have hfsq := hfprod.integrable_sq
  have hm : AEStronglyMeasurable (verticalCoefficient freq f) volume :=
    (hfprod.aestronglyMeasurable.mul (verticalMode_memLp hfreq).aestronglyMeasurable.comp_snd).integral_prod_right'
  have hs := split_memLp_vertical_slices f hf
  have hdom : ∀ᵐ r : PlanarPosition,
      (verticalCoefficient freq f r)^2 ≤ ∫ z : ℝ, f (r,z)^2 := by
    filter_upwards [hs] with r hr
    simpa only [verticalCoefficient,verticalMode_normalized hfreq,mul_one] using
      line_pair_sq_le (fun z => f (r,z)) (verticalMode freq) hr (verticalMode_memLp hfreq)
  have hi : Integrable (fun r : PlanarPosition => ∫ z : ℝ, f (r,z)^2) := hfsq.integral_prod_left
  have ha : Integrable (fun r => (verticalCoefficient freq f r)^2) :=
    hi.mono' (hm.pow 2) (hdom.mono (fun r hr => by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (verticalCoefficient freq f r))] using hr))
  refine ⟨(memLp_two_iff_integrable_sq hm).mpr ha, ?_⟩
  have h := integral_mono_ae ha hi hdom
  rw [← integral_prod _ hfsq] at h
  simpa only [Measure.volume_eq_prod] using h

theorem verticalCoefficient_sub_ae {freq : ℝ} (hfreq : 0 < freq)
    (f g : SplitPosition → ℝ) (hf : MemLp f 2) (hg : MemLp g 2) :
    verticalCoefficient freq (fun p => f p-g p) =ᵐ[volume]
      fun r => verticalCoefficient freq f r-verticalCoefficient freq g r := by
  filter_upwards [split_memLp_vertical_slices f hf,split_memLp_vertical_slices g hg] with r hr hr'
  unfold verticalCoefficient
  rw [show (fun z => (f (r,z)-g (r,z))*verticalMode freq z) =
    (fun z => f (r,z)*verticalMode freq z-g (r,z)*verticalMode freq z) from
      funext (fun z => sub_mul _ _ _)]
  simpa only [Pi.mul_apply] using
    integral_sub (hr.integrable_mul (verticalMode_memLp hfreq))
      (hr'.integrable_mul (verticalMode_memLp hfreq))

end ContinuumCoulomb

end

end OAI
