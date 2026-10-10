import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneMovingMass
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingConcentrationFamily

namespace OAI

/-! The actual translated concentration cutoffs retain scalar mass, up
to the inverse-square diffusion loss, along a rigid moving gate. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows VelocityDetector Set MeasureTheory
open scoped ContDiff

theorem concentration_mass_derivative_lower
    {T ν R C M : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hν : 0 ≤ ν) (hR : 0 < R) (hC : 0 ≤ C)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h))
    (hdiv : ∀ t x, PlanarHamiltonian.divergence (a t) x = 0)
    {c : ℝ → Plane} (hc : ContDiff ℝ ∞ c) (hb : ∃ B : ℝ, ∀ t, ‖c t‖ ≤ B)
    (hΔ : ∀ x, |scalarLaplacian massCutoff x| ≤ C)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (hwi : Integrable (w t)) (hwn : ∀ x, 0 ≤ w t x) (hwm : (∫ x, w t x) ≤ M)
    (hhn : ∀ x, 0 ≤ h t x)
    (hrigid : ∀ x, (∀ j, |x j - c t j| < 2 * R) → a t x = deriv c t) :
    ∃ d : ℝ, HasDerivAt (fun s => ∫ x, concentrationCutoff R (c s) x * w s x) d t ∧
      -(ν * (R⁻¹ ^ 2 * C) * M) ≤ d := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨K, hK, hs, hds⟩ := concentrationFamily_compact hR hB
  exact hw.moving_mass_derivative_lower
    (φ := fun s => concentrationCutoff R (c s))
    (φd := concentrationDerivative R c) hν (mul_nonneg (sq_nonneg _) hC) ha hh hdiv
    (concentrationCutoff_joint_smooth R hc) (concentrationDerivative_smooth R hc)
    (fun s x => concentrationCutoff_timeDerivative R hc s x) hK hs hds ht hwi hwn hwm
    (fun x => (concentrationCutoff_range R (c t) x).1) hhn
    (concentrationCutoff_laplacian hΔ R (c t))
    (concentrationCutoff_transport_cancel hR (a t) t hrigid)

theorem concentration_mass_retention
    {T ν R C M A B : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hν : 0 ≤ ν) (hR : 0 < R) (hC : 0 ≤ C)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h))
    (hdiv : ∀ t x, PlanarHamiltonian.divergence (a t) x = 0)
    {c : ℝ → Plane} (hc : ContDiff ℝ ∞ c) (hb : ∃ Q : ℝ, ∀ t, ‖c t‖ ≤ Q)
    (hΔ : ∀ x, |scalarLaplacian massCutoff x| ≤ C)
    (hwi : ∀ t ∈ Icc 0 T, Integrable (w t))
    (hwn : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ w t x)
    (hwm : ∀ t ∈ Icc 0 T, (∫ x, w t x) ≤ M)
    (hhn : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x)
    (hA : 0 ≤ A) (hAB : A ≤ B) (hBT : B ≤ T)
    (hrigid : ∀ t ∈ Ioo A B, ∀ x,
      (∀ j, |x j - c t j| < 2 * R) → a t x = deriv c t) :
    (∫ x, concentrationCutoff R (c A) x * w A x) -
        ν * (R⁻¹ ^ 2 * C) * M * (B - A) ≤
      ∫ x, concentrationCutoff R (c B) x * w B x := by
  let F : ℝ → ℝ := fun t => ∫ x, concentrationCutoff R (c t) x * w t x
  have hsub : Icc A B ⊆ Icc (0 : ℝ) T := Icc_subset_Icc hA hBT
  have hsub' : Ioo A B ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_of_le_of_lt hA ht.1, lt_of_lt_of_le ht.2 hBT⟩
  obtain ⟨Q, hQ⟩ := hb
  obtain ⟨K, hK, hs, _⟩ := concentrationFamily_compact hR hQ
  have hcont : ContinuousOn F (Icc 0 T) := by
    apply compact_supported_integral_continuousOn
      (g := fun p : ℝ × Plane => concentrationCutoff R (c p.1) p.2 * w p.1 p.2)
      (((concentrationCutoff_joint_smooth R hc).contDiffOn.mul hw.smooth).continuousOn) hK
    intro t x hx
    apply hs t
    exact fun hz => hx (by change concentrationCutoff R (c t) x * w t x = 0; rw [hz, zero_mul])
  have hd (t : ℝ) (ht : t ∈ Ioo A B) :
      ∃ d, HasDerivAt F d t ∧ -(ν * (R⁻¹ ^ 2 * C) * M) ≤ d :=
    concentration_mass_derivative_lower hw hν hR hC ha hh hdiv hc ⟨Q, hQ⟩ hΔ
      (hsub' ht) (hwi t (hsub (Ioo_subset_Icc_self ht)))
      (hwn t (hsub (Ioo_subset_Icc_self ht)))
      (hwm t (hsub (Ioo_subset_Icc_self ht)))
      (hhn t (hsub (Ioo_subset_Icc_self ht))) (hrigid t ht)
  apply lower_increment_of_derivative_bound hAB (hcont.mono hsub)
    (d := deriv F)
  · intro t ht
    obtain ⟨d, hd, _⟩ := hd t ht
    rw [hd.deriv]
    exact hd
  · intro t ht
    obtain ⟨d, hd, hb⟩ := hd t ht
    rw [hd.deriv]
    exact hb

end ForcedComputation.ExpandingDetector

end

end OAI
