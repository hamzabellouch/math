import OAI.Probability.SLE.Loewner.HalfPlaneDisplacementBound

namespace OAI

/-! Reading the hydrodynamic mass from a vertical displacement bound. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge

lemma hydrodynamic_mass_le_of_displacement {f : ℂ → ℂ} {a b : ℝ}
    (hcoef : Tendsto (fun z : ℂ => z*f z)
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 (-a:ℂ)))
    (hbound : ∀ z∈upperHalfPlane, ‖f z‖≤b/z.im) : a≤b := by
  apply le_of_tendsto (hydrodynamic_vertical_limits hcoef).2
  apply Eventually.of_forall
  intro n
  have hi := (Complex.im_le_norm (f (verticalInfinity n))).trans
    (hbound _ (verticalInfinity_mem n))
  have hy : 0<(n:ℝ)+1 := by positivity
  have hb := (le_div_iff₀ hy).mp (show (f (verticalInfinity n)).im≤b/((n:ℝ)+1) from by
    simpa only [verticalInfinity,mul_im,ofReal_re,I_im,mul_one,ofReal_im,I_re,mul_zero,add_zero]
      using hi)
  nlinarith

end SLEExactGauge

end

end OAI
