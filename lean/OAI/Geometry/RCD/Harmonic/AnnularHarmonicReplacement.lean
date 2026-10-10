import OAI.Geometry.RCD.Sobolev.HarmonicReplacementEnergy
import OAI.Geometry.RCD.Sobolev.UniformAnnularCoercivity

namespace OAI

/-! # Uniform normalized bounds for constructed harmonic replacements -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.annular_harmonic_replacement {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) :
    ∃ P : ℝ, 0<P ∧ ∀ (p : X) (r : ℝ), 0<r → -1≤K*(2*r)^2 →
      2*(hausdorff n X).real (ball p r)≤(hausdorff n X).real (ball p (2*r)) →
      ∀ (u : SobolevSpace (hausdorff n X) hX.quadratic) (m L E : ℝ),
        ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic u‖^2≤L*m →
        r^2*energyForm (hausdorff n X) hX.quadratic u u≤E*m →
        ∃ h : SobolevSpace (hausdorff n X) hX.quadratic,
          h-u∈SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p r) ∧
          IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) h ∧
          energyForm (hausdorff n X) hX.quadratic h h≤energyForm (hausdorff n X) hX.quadratic u u ∧
          ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic h‖^2≤(2*L+2*P*E)*m := by
  obtain ⟨P,hP,hp⟩ := hX.uniform_annular_coercivity hn
  refine ⟨P,hP,?_⟩
  intro p r hr hcurv hann u m L E hu he
  have hpr : 0≤P*r^2 := mul_nonneg hP.le (sq_nonneg _)
  obtain ⟨h,hb,hh⟩ := exists_harmonic_replacement (hausdorff n X) hX.quadratic
    (ball p r) hpr (hp p r hr hcurv hann) u
  refine ⟨h,hb,hh,harmonic_replacement_energy_le _ _ _ _ _ hb hh,?_⟩
  have hl := harmonic_replacement_l2_bound (hausdorff n X) hX.quadratic
    (ball p r) u h hb hh hpr (hp p r hr hcurv hann)
  have hpe := mul_le_mul_of_nonneg_left he (show 0≤2*P by positivity)
  nlinarith

end RegularPointCoordinates

end

end OAI
