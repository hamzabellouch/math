import OAI.Analysis.Mahler.SourceStokes

namespace OAI

open Set Filter MeasureTheory ContinuousAlternatingMap MahlerStokes
open scoped Topology Manifold

namespace Mahler
noncomputable section
variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

/-- The R^(-(k+1)) boundary restriction survives the actual oriented chart
integral, including its compact cutoff and its zero extension. -/
theorem chartBoundaryFlux_source_scaling (h : MassHypotheses n N m U f G) (k : ℕ)
    (Ψ : (Fin ((2*k+1)+1) → ℝ) ≃L[ℝ] ComplexEuclidean n)
    (p : RegularBoundaryPatch ((2*k+1)+1) (Ψ ⁻¹' U) (fun x => tau f (Ψ x)))
    {R : ℝ} (hR : 0 < R) (ρ : (Fin ((2*k+1)+1) → ℝ) → ℝ)
    (hρ : tsupport ρ ⊆ p.domain) :
    chartBoundaryFlux p.chart p.coordinate R (fun z => ρ z • sourceCoordinateForm Ψ (logTau f) k z) =
      (R⁻¹)^(k+1) * chartBoundaryFlux p.chart p.coordinate R
        (fun z => ρ z • sourceCoordinateForm Ψ (energy f) k z) := by
  have he (y : Fin (2*k+1) → ℝ) :
      extendedChartForm p.chart (fun z => ρ z • sourceCoordinateForm Ψ (logTau f) k z)
        (p.coordinate.insertNth R y) (p.coordinate.removeNth (coordinateBasis ((2*k+1)+1))) =
      (R⁻¹)^(k+1) * extendedChartForm p.chart
        (fun z => ρ z • sourceCoordinateForm Ψ (energy f) k z)
          (p.coordinate.insertNth R y) (p.coordinate.removeNth (coordinateBasis ((2*k+1)+1))) := by
    by_cases hy : p.coordinate.insertNth R y ∈ p.chart.target
    · by_cases hz : ρ (p.chart.symm (p.coordinate.insertNth R y)) = 0
      · simp [extendedChartForm, hy, pullbackForm, hz]
      · have hdom : p.chart.symm (p.coordinate.insertNth R y) ∈ p.domain :=
          hρ (subset_tsupport ρ hz)
        have hface : y ∈ p.faceDomain R := ⟨hy, hdom⟩
        have hψ : DifferentiableAt ℝ p.chart.symm (coordinateFace p.coordinate R y) :=
          (p.smooth_inverse.contDiffAt (p.chart.open_target.mem_nhds hy)).differentiableAt (by norm_num)
        have hf := congrArg (fun a => a (coordinateBasis (2*k+1)))
          (sourceCoordinateForm_regular_face h Ψ p hR hface k)
        simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hf
        unfold RegularBoundaryPatch.faceParam at hf
        rw [pullback_coordinateFace_coefficient p.coordinate R p.chart.symm _ y hψ,
          pullback_coordinateFace_coefficient p.coordinate R p.chart.symm _ y hψ] at hf
        simp only [pullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply] at hf
        simp only [extendedChartForm, indicator_of_mem hy, pullbackForm,
          ContinuousAlternatingMap.compContinuousLinearMap_apply,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        unfold coordinateFace at hf
        rw [hf]
        ring
    · simp [extendedChartForm, hy]
  unfold chartBoundaryFlux
  simp_rw [he]
  rw [integral_const_mul]
  ring

/-- The Stokes identity for coordinate flux forms, with all charts
eliminated from the conclusion. The volume integrands are
exterior derivatives of those forms; equality to Hessian top
powers is not asserted by this theorem. -/
theorem source_punctured_scaled_extDeriv (h : MassHypotheses n N m U f G) (k : ℕ)
    (Ψ : (Fin ((2*k+1)+1) → ℝ) ≃L[ℝ] ComplexEuclidean n)
    {R r : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hreg : ∀ x ∈ U, tau f x = R → fderiv ℝ (tau f) x ≠ 0)
    (hr : 0 < r)
    (hB : coordClosedBall ((2*k+1)+1) r ⊆ regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R) :
    (R⁻¹)^(k+1) *
      (∫ x in regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R,
        extDeriv (sourceCoordinateForm Ψ (energy f) k) x (coordinateBasis ((2*k+1)+1))) -
      sphereFlux r (sourceCoordinateForm Ψ (logTau f) k) =
      ∫ x in regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R \ coordClosedBall ((2*k+1)+1) r,
        extDeriv (sourceCoordinateForm Ψ (logTau f) k) x (coordinateBasis ((2*k+1)+1)) := by
  obtain ⟨a, W, ρ, _, _, _, hρsub, _, hE, hL⟩ :=
    exists_source_stokes_partition h k Ψ hR hR1 hreg
  have hs :
      (∑ i : a.Index, chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R
        (fun z => ρ (some i) z • sourceCoordinateForm Ψ (logTau f) k z)) =
      (R⁻¹)^(k+1) *
        (∑ i : a.Index, chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R
          (fun z => ρ (some i) z • sourceCoordinateForm Ψ (energy f) k z)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact chartBoundaryFlux_source_scaling h k Ψ (a.patch i) hR (ρ (some i)) (hρsub (some i))
  have hl := hL r hr hB
  rw [hs, ← hE] at hl
  exact hl

end
end Mahler

end OAI
