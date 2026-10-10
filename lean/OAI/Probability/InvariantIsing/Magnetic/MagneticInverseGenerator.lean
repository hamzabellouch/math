import OAI.Probability.InvariantIsing.Magnetic.MagneticInverseVariation

namespace OAI

/-! The inverse-mean generator identities. The hypotheses are the
ordinary backward Gaussian derivative identities, and the inverse-coordinate
form follows from the proved implicit-bias variation rule. -/

noncomputable section
open IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma inverse_curvature_generator {U Q : ℝ × ℝ → ℝ} {b : ℝ → ℝ}
    {t s m q r w ζ : ℝ} (hq : q ≠ 0) (hb : ContinuousAt b t)
    (hU : HasFDerivAt U (pairLinear (-r / 2 - ζ * m * q) q) (t, b t))
    (he : ∀ᶠ v in 𝓝 t, U (v, b v) = s)
    (hQ : HasFDerivAt Q (pairLinear (-w / 2 - ζ * (q ^ 2 + m * r)) r) (t, b t)) :
    HasDerivAt (fun v => Q (v, b v))
      (-(q ^ 2 / 2) * (w / q ^ 2 - r ^ 2 / q ^ 3) - ζ * q ^ 2) t := by
  have hd := inverse_mean_curvature_variation hb hq hU he hQ
  convert hd using 1
  field_simp [hq]
  ring

lemma inverse_continuation_generator {U V : ℝ × ℝ → ℝ} {b : ℝ → ℝ}
    {t s m q r a d ζ : ℝ} (hq : q ≠ 0) (hb : ContinuousAt b t)
    (hU : HasFDerivAt U (pairLinear (-r / 2 - ζ * m * q) q) (t, b t))
    (he : ∀ᶠ v in 𝓝 t, U (v, b v) = s)
    (hV : HasFDerivAt V (pairLinear (-d / 2 - ζ * m * a) a) (t, b t)) :
    HasDerivAt (fun v => V (v, b v))
      (-(q ^ 2 / 2) * (d / q ^ 2 - a * r / q ^ 3)) t := by
  have hd := inverse_mean_curvature_variation hb hq hU he hV
  convert hd using 1
  field_simp [hq]
  ring

/-- The zeroth-order coefficient of the twice differentiated inverse
continuation equation only needs the ratio of fourth and second ordinary
derivatives: the apparent square of the third derivative cancels. -/
lemma inverse_diffusion_second {q r w : ℝ} (hq : q ≠ 0) :
    2 * (r / q) ^ 2 + 2 * q * (w / q ^ 2 - r ^ 2 / q ^ 3) = 2 * w / q := by
  field_simp [hq]
  ring

end InvariantIsing

end

end OAI
