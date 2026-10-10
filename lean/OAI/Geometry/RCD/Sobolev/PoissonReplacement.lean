import OAI.Geometry.RCD.Sobolev.DirichletPoincare

namespace OAI

/-! # Constant-Laplacian replacements with prescribed Sobolev boundary data -/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Integration against an actual `L²` source on the Dirichlet space. -/
def dirichletSource (Ω : Set X) (g : Lp ℝ 2 μ) :
    SobolevSpace.dirichlet μ hQ Ω →L[ℝ] ℝ :=
  (innerSL ℝ g).comp ((SobolevSpace.toLpCLM μ hQ).comp
    (SobolevSpace.dirichlet μ hQ Ω).subtypeL)

theorem dirichletSource_apply (Ω : Set X) (g : Lp ℝ 2 μ)
    (φ : SobolevSpace.dirichlet μ hQ Ω) :
    dirichletSource μ hQ Ω g φ = inner ℝ g (SobolevSpace.toLp μ hQ φ.val) := rfl

/-- The finite-measure indicator is the constant source on the domain. -/
theorem dirichletSource_indicator (Ω : Set X) (hΩ : MeasurableSet Ω)
    (hfin : μ Ω ≠ ∞) (c : ℝ) (φ : SobolevSpace.dirichlet μ hQ Ω) :
    dirichletSource μ hQ Ω (indicatorConstLp 2 hΩ hfin c) φ =
      c * ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ := by
  rw [dirichletSource_apply, L2.inner_def]
  calc
    _ = ∫ x, Ω.indicator (fun x => c * SobolevSpace.toLp μ hQ φ.val x) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hΩ) (hμs := hfin) (c := c)] with x hx
      rw [hx]
      by_cases hm : x ∈ Ω <;> simp [hm, mul_comm]
    _ = _ := by rw [integral_indicator hΩ, integral_const_mul]

omit [MetricSpace X] in
theorem norm_indicator_source_sq (Ω : Set X) (hΩ : MeasurableSet Ω)
    (hfin : μ Ω ≠ ∞) (c : ℝ) :
    ‖indicatorConstLp 2 hΩ hfin c‖ ^ 2 = c ^ 2 * μ.real Ω := by
  rw [← lp_integral_square_eq_norm_square]
  calc
    _ = ∫ x, Ω.indicator (fun _ => c ^ 2) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hΩ) (hμs := hfin) (c := c)] with x hx
      rw [hx]
      by_cases hm : x ∈ Ω <;> simp [hm]
    _ = c ^ 2 * μ.real Ω := by
      rw [integral_indicator hΩ]
      simp [mul_comm]

/-- Testing a Dirichlet solution with itself gives its quantitative energy
bound from the `L²` source and the Poincare constant. -/
theorem dirichlet_solution_energy_le (Ω : Set X) {P : ℝ} (hP : 0 ≤ P)
    (hbound : ∀ f : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ f.val‖ ^ 2 ≤ P * energyForm μ hQ f.val f.val)
    (g : Lp ℝ 2 μ) (f : SobolevSpace.dirichlet μ hQ Ω)
    (hsolve : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      energyForm μ hQ f.val φ.val = -dirichletSource μ hQ Ω g φ) :
    energyForm μ hQ f.val f.val ≤ P * ‖g‖ ^ 2 := by
  let e := energyForm μ hQ f.val f.val
  have he : 0 ≤ e := by
    dsimp [e]
    rw [energyForm_self]
    exact mul_nonneg (by norm_num) (SobolevSpace.energy_nonneg μ hQ f.val)
  have hcs : |e| ≤ ‖g‖ * ‖SobolevSpace.toLp μ hQ f.val‖ := by
    dsimp [e]
    rw [hsolve f, dirichletSource_apply, abs_neg]
    exact abs_real_inner_le_norm _ _
  have hsq := (sq_le_sq₀ (abs_nonneg e)
    (mul_nonneg (norm_nonneg g) (norm_nonneg _))).mpr hcs
  rw [sq_abs, mul_pow] at hsq
  have hb := mul_le_mul_of_nonneg_left (hbound f) (sq_nonneg ‖g‖)
  change ‖g‖ ^ 2 * ‖SobolevSpace.toLp μ hQ f.val‖ ^ 2 ≤ ‖g‖ ^ 2 * (P * e) at hb
  by_cases hz : e = 0
  · change e ≤ P * ‖g‖ ^ 2
    rw [hz]
    exact mul_nonneg hP (sq_nonneg _)
  · have hp : 0 < e := lt_of_le_of_ne he (Ne.symm hz)
    change e ≤ P * ‖g‖ ^ 2
    apply (mul_le_mul_iff_left₀ hp).mp
    calc
      e * e = e ^ 2 := by ring
      _ ≤ ‖g‖ ^ 2 * (P * e) := hsq.trans hb
      _ = (P * ‖g‖ ^ 2) * e := by ring

/-- Solves `Delta v = c` with `v-u` in the genuine zero-boundary Sobolev
space. Only the displayed Poincare bound and finite domain measure are used. -/
theorem exists_constant_laplacian_replacement (Ω : Set X) (hΩ : MeasurableSet Ω)
    (hfin : μ Ω ≠ ∞) {P : ℝ} (hP : 0 ≤ P)
    (hbound : ∀ f : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ f.val‖ ^ 2 ≤ P * energyForm μ hQ f.val f.val)
    (c : ℝ) (u : SobolevSpace μ hQ) :
    ∃ v : SobolevSpace μ hQ, v - u ∈ SobolevSpace.dirichlet μ hQ Ω ∧
      ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
        energyForm μ hQ v φ.val = -c * ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ := by
  let F := -dirichletSource μ hQ Ω (indicatorConstLp 2 hΩ hfin c) -
    (sobolevEnergyForm μ hQ u).comp (SobolevSpace.dirichlet μ hQ Ω).subtypeL
  obtain ⟨w, hw, _⟩ := existsUnique_dirichlet_solution μ hQ Ω hP hbound F
  refine ⟨u + w.val, ?_, ?_⟩
  · simpa only [add_sub_cancel_left] using w.property
  · intro φ
    have he := hw φ
    change energyForm μ hQ w.val φ.val =
      -dirichletSource μ hQ Ω (indicatorConstLp 2 hΩ hfin c) φ -
        energyForm μ hQ u φ.val at he
    rw [dirichletSource_indicator] at he
    rw [energyForm_add_left]
    linarith

variable [BorelSpace X]

/-- The RCD hypotheses supply both the finite measure and the Poincare
bound used by the constant-Laplacian construction. -/
theorem NoncollapsedRCD.exists_constant_laplacian_replacement
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R) (Ω B : Set X)
    (hΩ : MeasurableSet Ω) (hB : MeasurableSet B)
    (hΩ0 : hausdorff n X Ω ≠ 0) (hB0 : hausdorff n X B ≠ 0)
    (hsΩ : Ω ⊆ Metric.closedBall p R) (hsB : B ⊆ Metric.closedBall p R)
    (hBΩ : B ⊆ Ωᶜ) (c : ℝ) (u : SobolevSpace (hausdorff n X) hX.quadratic) :
    ∃ v : SobolevSpace (hausdorff n X) hX.quadratic,
      v - u ∈ SobolevSpace.dirichlet (hausdorff n X) hX.quadratic Ω ∧
      ∀ φ : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic Ω,
        energyForm (hausdorff n X) hX.quadratic v φ.val =
          -c * ∫ x in Ω, SobolevSpace.toLp (hausdorff n X) hX.quadratic φ.val x ∂hausdorff n X := by
  obtain ⟨P, hP, hbound⟩ := hX.exists_dirichlet_poincare K n hn p hR Ω B
    hΩ hB hΩ0 hB0 hsΩ hsB hBΩ
  have hfin : hausdorff n X Ω ≠ ∞ :=
    ne_of_lt (hX.finiteOnBounded Ω (Metric.isBounded_closedBall.subset hsΩ))
  exact RegularPointCoordinates.exists_constant_laplacian_replacement
    (hausdorff n X) hX.quadratic Ω hΩ hfin hP hbound c u

end RegularPointCoordinates

end

end OAI
