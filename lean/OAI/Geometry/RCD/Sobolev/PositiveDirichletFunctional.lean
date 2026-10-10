import OAI.Geometry.RCD.Metric.PositiveSourceMeasure
import OAI.Geometry.RCD.Sobolev.DirichletMaximum

namespace OAI

/-!
# Positive source functionals on the Dirichlet space

Positivity on the nonnegative Lipschitz core passes to all nonnegative
Dirichlet tests by positive-part approximation and weak energy convergence.
-/

open Set MeasureTheory Filter
open scoped NNReal InnerProductSpace Topology

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Positivity on the core suffices, without pointwise evaluation of
Sobolev representatives against the source. -/
theorem dirichlet_test_nonneg_of_core (Ω : Set X) (H : SobolevSpace μ hQ)
    (hcore : ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (C : ℝ≥0),
      LipschitzWith C v → HasCompactSupport v → tsupport v ⊆ Ω →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v → (∀ x, 0 ≤ v x) →
      0 ≤ energyForm μ hQ H ψ)
    (φ : SobolevSpace.dirichlet μ hQ Ω)
    (hφ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x) :
    0 ≤ energyForm μ hQ H φ.val := by
  let pos : ℝ → ℝ := fun t => max t 0
  have hp : LipschitzWith 1 pos :=
    (LipschitzWith.id : LipschitzWith 1 (fun t : ℝ => t)).max_const 0
  have hp0 : pos 0 = 0 := max_self 0
  obtain ⟨fs, hfs, hlim⟩ := mem_closure_iff_seq_limit.mp φ.property
  obtain ⟨D, hD⟩ := (Metric.isBounded_range_of_tendsto fs hlim).exists_norm_le
  let T := fun i => SobolevSpace.compContraction μ hQ hp hp0 (fs i)
  have hTb (i : ℕ) : ‖T i‖ ≤ D :=
    (SobolevSpace.norm_compContraction_le μ hQ hp hp0 (fs i)).trans
      (hD (fs i) (mem_range_self i))
  have hclip : hp.compLp hp0 (SobolevSpace.toLp μ hQ φ.val) =
      SobolevSpace.toLp μ hQ φ.val := by
    apply Lp.ext
    filter_upwards [hp.coeFn_compLp hp0 (SobolevSpace.toLp μ hQ φ.val), hφ] with x hx hb
    rw [hx]
    exact max_eq_left hb
  have hTl : Tendsto (fun i => SobolevSpace.toLp μ hQ (T i)) atTop
      (𝓝 (SobolevSpace.toLp μ hQ φ.val)) := by
    have ht := (hp.continuous_compLp hp0).continuousAt.tendsto.comp
      ((SobolevSpace.toLpCLM μ hQ).continuous.continuousAt.tendsto.comp hlim)
    change Tendsto (fun i => hp.compLp hp0 (SobolevSpace.toLp μ hQ (fs i))) atTop
      (𝓝 (hp.compLp hp0 (SobolevSpace.toLp μ hQ φ.val))) at ht
    rw [hclip] at ht
    exact ht
  rw [energyForm_comm μ hQ H φ.val]
  apply ge_of_tendsto (SobolevSpace.energyForm_tendsto_of_toLp_tendsto_bounded μ hQ hTb hTl H)
  apply Eventually.of_forall
  intro i
  rw [energyForm_comm μ hQ (T i) H]
  obtain ⟨g, C, hg, hgc, hgs, hfg⟩ := hfs i
  exact hcore (T i) (pos ∘ g) C (by simpa only [one_mul] using hp.comp hg)
    (hgc.comp_left hp0) ((tsupport_comp_subset hp0 g).trans hgs)
    ((hp.coeFn_compLp hp0 (SobolevSpace.toLp μ hQ (fs i))).trans (hfg.fun_comp pos))
    (fun x => le_max_right _ _)

/-- A positive measure source is a positive functional on every
nonnegative Dirichlet test. -/
theorem IsDirichletMeasureSource.test_nonneg (Ω : Set X)
    (H : SobolevSpace μ hQ) (σ : Measure X)
    (hsource : IsDirichletMeasureSource μ hQ Ω H σ)
    (φ : SobolevSpace.dirichlet μ hQ Ω)
    (hφ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x) :
    0 ≤ energyForm μ hQ H φ.val := by
  apply dirichlet_test_nonneg_of_core μ hQ Ω H _ φ hφ
  intro ψ v C hv hvc hs hψ hv0
  rw [hsource ψ v C hv hvc hs hψ]
  exact integral_nonneg hv0

/-- Coercivity and positivity of the measure source imply nonnegativity
of its Dirichlet solution. -/
theorem IsDirichletMeasureSource.solution_nonneg (Ω : Set X)
    {P : ℝ} (hP : 0 ≤ P)
    (hpoin : ∀ v : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ v.val‖ ^ 2 ≤ P * energyForm μ hQ v.val v.val)
    (H : SobolevSpace.dirichlet μ hQ Ω) (σ : Measure X)
    (hsource : IsDirichletMeasureSource μ hQ Ω H.val σ) :
    ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H.val x := by
  let F := (sobolevEnergyForm μ hQ H.val).comp (SobolevSpace.dirichlet μ hQ Ω).subtypeL
  exact dirichlet_solution_nonneg μ hQ Ω hP hpoin F
    (fun φ hφ => hsource.test_nonneg μ hQ Ω H.val σ φ hφ) H (fun _ => rfl)

end RegularPointCoordinates

end

end OAI
