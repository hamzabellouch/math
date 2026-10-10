import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulomb

namespace OAI

/-! Actual strict positivity and symmetry of the direct Coulomb coefficients. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedDensity_potential_positive {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) :
    0 < NeutralAtom.potentialOf (localizedDensity freq u) x := by
  have hn := localizedDensity_potential_nonnegative freq u x
  by_contra h
  have hz : NeutralAtom.potentialOf (localizedDensity freq u) x = 0 := by linarith
  have he := (integral_eq_zero_iff_of_nonneg
    (fun y => mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
      (localizedDensity_nonnegative freq u y))
    (localizedDensity_coulomb_integrable_bound hfreq u x).1).mp hz
  have hf : ∀ᵐ y : Position, False := by
    filter_upwards [he, volume.ae_ne x] with y hy hxy
    have hk : 0 < NeutralAtom.coulombKernel (x - y) :=
      inv_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hxy.symm))
    exact (mul_pos hk (localizedDensity_positive hfreq u y)).ne' hy
  obtain ⟨y, hy⟩ := hf.exists
  exact hy

theorem localizedCoulombCoeff_positive {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) : 0 < localizedCoulombCoeff freq u v :=
  integral_pos_of_integrable_nonneg_nonzero
    ((localizedDensity_continuous freq u).mul (localizedDensity_potential_continuous hfreq v))
    (localizedCoulombCoeff_integrable hfreq u v)
    (fun x => mul_nonneg (localizedDensity_nonnegative freq u x)
      (localizedDensity_potential_nonnegative freq v x))
    (mul_pos (localizedDensity_positive hfreq u 0)
      (localizedDensity_potential_positive hfreq v 0)).ne'

theorem localizedCoulomb_product_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) :
    Integrable (fun p : Position × Position => localizedDensity freq u p.1 *
      (NeutralAtom.coulombKernel (p.1 - p.2) * localizedDensity freq v p.2))
      ((volume : Measure Position).prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : Position × Position => localizedDensity freq u p.1 *
        (NeutralAtom.coulombKernel (p.1 - p.2) * localizedDensity freq v p.2))
      ((volume : Measure Position).prod volume) :=
    (((localizedDensity_continuous freq u).measurable.comp measurable_fst).mul
      ((NeutralAtom.measurable_coulombKernel.comp (measurable_fst.sub measurable_snd)).mul
        ((localizedDensity_continuous freq v).measurable.comp measurable_snd))).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun x =>
      (localizedDensity_coulomb_integrable_bound hfreq v x).1.const_mul
        (localizedDensity freq u x))
  · have hn (x y : Position) :
        ‖localizedDensity freq u x *
          (NeutralAtom.coulombKernel (x - y) * localizedDensity freq v y)‖ =
        localizedDensity freq u x *
          (NeutralAtom.coulombKernel (x - y) * localizedDensity freq v y) :=
      Real.norm_of_nonneg (mul_nonneg (localizedDensity_nonnegative freq u x)
        (mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
          (localizedDensity_nonnegative freq v y)))
    simp_rw [hn, integral_const_mul]
    exact localizedCoulombCoeff_integrable hfreq u v

theorem localizedCoulombCoeff_symmetric {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) : localizedCoulombCoeff freq u v = localizedCoulombCoeff freq v u := by
  unfold localizedCoulombCoeff NeutralAtom.potentialOf
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap (localizedCoulomb_product_integrable hfreq u v)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      simp only [NeutralAtom.coulombKernel, norm_sub_rev x y]
      ring))

end ContinuumCoulomb

end

end OAI
