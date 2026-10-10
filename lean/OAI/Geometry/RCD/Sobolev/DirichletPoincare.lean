import OAI.Geometry.RCD.Sobolev.DirichletPoisson

namespace OAI

/-!
# RCD coercivity for the actual zero-boundary Sobolev space

A positive-measure exterior set gives the Poincare constant required by
the Dirichlet solver. The estimate is deduced from the existing RCD
transport proof of integral coercivity.
-/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
theorem lp_integral_square_eq_norm_square (μ : Measure X) (u : Lp ℝ 2 μ) :
    (∫ x, (u x) ^ 2 ∂μ) = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [L2.inner_def, Real.inner_apply, pow_two]

/-- A bounded Dirichlet domain with positive-measure exterior has an
explicit finite Poincare constant. -/
theorem NoncollapsedRCD.exists_dirichlet_poincare
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R) (Ω B : Set X)
    (hΩ : MeasurableSet Ω) (hB : MeasurableSet B)
    (hΩ0 : hausdorff n X Ω ≠ 0) (hB0 : hausdorff n X B ≠ 0)
    (hsΩ : Ω ⊆ Metric.closedBall p R) (hsB : B ⊆ Metric.closedBall p R)
    (hBΩ : B ⊆ Ωᶜ) :
    ∃ P : ℝ, 0 ≤ P ∧
      ∀ f : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic Ω,
        ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic f.val‖ ^ 2 ≤
          P * energyForm (hausdorff n X) hX.quadratic f.val f.val := by
  let μ := hausdorff n X
  let P := μ.real Ω * (2 * R) ^ 2 *
    (compressionBudget K n (2 * R) (max (μ Ω)⁻¹ (μ B)⁻¹)).toReal
  refine ⟨P, by dsimp [P]; positivity, fun f => ?_⟩
  let u := SobolevSpace.toLp μ hX.quadratic f.val
  let g := SobolevSpace.minimalSlope μ hX.quadratic f.val
  have hz : u =ᵐ[μ.restrict Ωᶜ] 0 :=
    SobolevSpace.dirichlet_zero_off μ hX.quadratic Ω hΩ f
  have hzB : u =ᵐ[μ.restrict B] 0 :=
    ae_restrict_of_ae_restrict_of_subset hBΩ hz
  have hi := hX.dirichlet_integral_coercivity K n hn p hR hΩ hB hΩ0 hB0 hsΩ hsB
    (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic f.val) hzB
  have hu : (∫ x in Ω, (u x) ^ 2 ∂μ) = ‖u‖ ^ 2 := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero, lp_integral_square_eq_norm_square]
    filter_upwards [(ae_restrict_iff' hΩ.compl).mp hz] with x hx hnot
    simp [hx hnot]
  have hg : (∫ x, (g x) ^ 2 ∂μ) = energyForm μ hX.quadratic f.val f.val := by
    rw [lp_integral_square_eq_norm_square]
    exact (SobolevSpace.minimalSlope_norm_sq μ hX.quadratic f.val).trans
      (energyForm_self μ hX.quadratic f.val).symm
  change (∫ x in Ω, (u x) ^ 2 ∂μ) ≤ P * (∫ x, (g x) ^ 2 ∂μ) at hi
  rw [hu, hg] at hi
  exact hi

/-- The harmonic replacement exists for the genuine RCD Dirichlet form;
its coercivity is derived above, rather than supplied as an extra input. -/
theorem NoncollapsedRCD.exists_dirichlet_harmonic_replacement
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R) (Ω B : Set X)
    (hΩ : MeasurableSet Ω) (hB : MeasurableSet B)
    (hΩ0 : hausdorff n X Ω ≠ 0) (hB0 : hausdorff n X B ≠ 0)
    (hsΩ : Ω ⊆ Metric.closedBall p R) (hsB : B ⊆ Metric.closedBall p R)
    (hBΩ : B ⊆ Ωᶜ) (u : SobolevSpace (hausdorff n X) hX.quadratic) :
    ∃ h : SobolevSpace (hausdorff n X) hX.quadratic,
      h - u ∈ SobolevSpace.dirichlet (hausdorff n X) hX.quadratic Ω ∧
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic Ω h := by
  obtain ⟨P, hP, hbound⟩ := hX.exists_dirichlet_poincare K n hn p hR Ω B
    hΩ hB hΩ0 hB0 hsΩ hsB hBΩ
  exact exists_harmonic_replacement (hausdorff n X) hX.quadratic Ω hP hbound u

/-- Componentwise replacement constructs the full harmonic coordinate
column without assuming a harmonic solution as data. -/
theorem NoncollapsedRCD.exists_dirichlet_harmonic_column
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R) (Ω B : Set X)
    (hΩ : MeasurableSet Ω) (hB : MeasurableSet B)
    (hΩ0 : hausdorff n X Ω ≠ 0) (hB0 : hausdorff n X B ≠ 0)
    (hsΩ : Ω ⊆ Metric.closedBall p R) (hsB : B ⊆ Metric.closedBall p R)
    (hBΩ : B ⊆ Ωᶜ) (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) :
    ∃ h : Fin n → SobolevSpace (hausdorff n X) hX.quadratic,
      ∀ a, h a - u a ∈ SobolevSpace.dirichlet (hausdorff n X) hX.quadratic Ω ∧
        IsSobolevHarmonicOn (hausdorff n X) hX.quadratic Ω (h a) := by
  classical
  exact Classical.axiomOfChoice fun a =>
    hX.exists_dirichlet_harmonic_replacement K n hn p hR Ω B hΩ hB hΩ0 hB0 hsΩ hsB hBΩ (u a)

end RegularPointCoordinates

end

end OAI
