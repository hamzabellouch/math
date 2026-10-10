import OAI.Analysis.TriangularHilbert.Coordinates

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Heat Filter
noncomputable section

lemma cyclicHard_coordinate_output (F G : Plane → ℂ) (z : Plane) (r R : ℝ) :
    cyclicKernelOutput (cyclicB F) (cyclicC G) (hardKernel r R) (-z) =
      ∫ t : ℝ, F (z.1+t,z.2)*G (z.1,z.2+t)*(hardKernel r R t:ℂ) := by
  rw [cyclicKernelOutput,← integral_add_right_eq_self _ (z.1+z.2)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by simpa only [add_assoc] using cyclicHard_coordinate_integrand F G z r R t)

lemma hardIntegrand_eq_indicator_ae (F G : Plane → ℂ) (z : Plane) {r R : ℝ} (hR : r ≤ R) :
    (fun t : ℝ => F (z.1+t,z.2)*G (z.1,z.2+t)*(hardKernel r R t:ℂ)) =ᵐ[volume]
      (annulus r R).indicator (integrand F G z) := by
  filter_upwards [hardKernel_eq_indicator_ae hR] with t ht
  classical
  by_cases hm : t ∈ annulus r R
  · rw [Set.indicator_of_mem hm] at ht
    rw [ht,Set.indicator_of_mem hm]
    simp only [integrand,div_eq_mul_inv,one_mul,Complex.ofReal_inv]
  · rw [Set.indicator_of_notMem hm] at ht
    simp only [ht,Complex.ofReal_zero,mul_zero,Set.indicator_of_notMem hm]

lemma truncation_eq_cyclicHard (F G : Plane → ℂ) (z : Plane) (E : Endpoints) :
    truncation F G E z = cyclicKernelOutput (cyclicB F) (cyclicC G) (hardKernel E.lower E.upper) (-z) := by
  rw [cyclicHard_coordinate_output,integral_congr_ae (hardIntegrand_eq_indicator_ae F G z E.lower_lt_upper.le),
    integral_indicator (measurableSet_annulus E.lower E.upper)]
  rfl

lemma Heat.CubicSliceGood.integrableOn_annulus {F G : Plane → ℂ} {z : Plane}
    (hz : CubicSliceGood (cyclicB F) (cyclicC G) (-z))
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) : IntegrableOn (integrand F G z) (annulus r R) := by
  have hi := hz.integrable_hard hr hR
  have ht := ((measurePreserving_add_right (volume : Measure ℝ) (z.1+z.2)).integrable_comp hi.aestronglyMeasurable).mpr hi
  have hi' : Integrable (fun t : ℝ => F (z.1+t,z.2)*G (z.1,z.2+t)*(hardKernel r R t:ℂ)) := by
    convert ht using 1
    funext t
    simpa only [Function.comp_apply,add_assoc] using (cyclicHard_coordinate_integrand F G z r R t).symm
  exact (integrable_indicator_iff (measurableSet_annulus r R)).mp
    (hi'.congr (hardIntegrand_eq_indicator_ae F G z hR))

lemma Heat.CubicSliceGood.goodPoint {F G : Plane → ℂ} {z : Plane}
    (hz : CubicSliceGood (cyclicB F) (cyclicC G) (-z)) : GoodPoint F G z := by
  intro n
  apply hz.integrableOn_annulus
  · positivity
  · apply (div_le_iff₀ (show (0:ℝ) < n+2 by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma ae_goodPoint (F G : Plane → ℂ) (hF : MemLp F 3 volume) (hG : MemLp G 3 volume) :
    ∀ᵐ z : Plane, GoodPoint F G z := by
  filter_upwards [measurePreserving_reflect.quasiMeasurePreserving.ae
    (ae_cubicSliceGood (cyclicB F) (cyclicC G) (memLp_cyclicB hF) (memLp_cyclicC hG))] with z hz
  exact hz.goodPoint
end
end TriangularHilbert
end

end OAI
