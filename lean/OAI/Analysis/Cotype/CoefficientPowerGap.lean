import OAI.Analysis.Cotype.SectorResolvent
import OAI.Analysis.Cotype.VerticalTimeCoefficient
import OAI.Analysis.Cotype.FiniteContour

namespace OAI

noncomputable section
namespace Cotype

theorem projectionLinearCoefficient_bound_of_power_gap
    {N : ℕ} (hN : 0 < N) {C : ℝ} (hC : 0 ≤ C)
    (hC2 : C < (2 : ℝ)^N) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [CompleteSpace Y] (m : ℕ) (P : Fin m → Y →L[ℝ] Y),
        (∀ i, P i * P i = P i) →
        (∀ i j, Commute (P i) (P j)) →
        (∀ i y, ‖P i y‖ ≤ ‖y‖) →
        (∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ y : Y,
          ‖((1-projectionSemigroup P r)^N) y‖ ≤ C*‖y‖) →
        ∀ y : Y, ‖projectionLinearCoefficient P y‖ ≤ K*‖y‖ := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨a, M, ha, hM, hres⟩ := uniform_projectionResolvent_bound_of_power_gap hC hC2
  obtain ⟨T, B, _hT, hB, hcontour⟩ :=
    finiteLaplaceSum_vertical_bound_of_sector_resolvent ha hM
  refine ⟨B / Real.exp (-T), div_nonneg hB (Real.exp_pos _).le, ?_⟩
  intro Y _ _ _ m P hp hc hP hgap y
  apply projectionLinearCoefficient_bound_of_vertical_time P hc
  intro τ hτ
  rw [complexProjectionTime_spectral]
  have hb := hcontour (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) (Cube m)
    (fun ε => (projectionDegree ε : ℝ))
    (fun ε => complexDualLift (projectionPattern P ε))
    (fun ε => Nat.cast_nonneg (projectionDegree ε))
    (by
      intro z hz hcone
      simpa only [projectionResolvent, complexSpectralEval, Complex.ofReal_natCast] using
        hres Y m P hp hc hP hgap z hz hcone) τ hτ
  simpa only [Complex.ofReal_natCast] using hb

end Cotype

end

end OAI
