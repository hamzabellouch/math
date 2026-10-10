import OAI.Geometry.RCD.Sobolev.PositiveDirichletFunctional
import OAI.Geometry.RCD.Harmonic.UpperLevelCaccioppoli

namespace OAI

/-! # Weak subsolutions and nonnegative Dirichlet tests -/

open Set Filter MeasureTheory
open scoped NNReal InnerProductSpace Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The distributional inequality `Δu ≥ -a u`, expressed using only
the actual Sobolev energy form and L² pairing. -/
def IsWeakSubsolutionOn (Ω : Set X) (u : SobolevSpace μ hQ) (a : ℝ) : Prop :=
  ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
    (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x) →
    energyForm μ hQ u φ.val ≤ a*inner ℝ (SobolevSpace.toLp μ hQ u) (SobolevSpace.toLp μ hQ φ.val)

theorem IsWeakSubsolutionOn.smul {Ω : Set X} {u : SobolevSpace μ hQ} {a : ℝ}
    (hu : IsWeakSubsolutionOn μ hQ Ω u a) (c : ℝ) (hc : 0 ≤ c) :
    IsWeakSubsolutionOn μ hQ Ω (c • u) a := by
  intro φ hφ
  have hh := mul_le_mul_of_nonneg_left (hu φ hφ) hc
  rw [energyForm_smul_left,map_smul,real_inner_smul_left]
  nlinarith only [hh]

/-- Positive-part approximation of the Lipschitz core extends the
distributional inequality to every nonnegative Dirichlet test. -/
theorem weakSubsolution_of_core (Ω : Set X) (u : SobolevSpace μ hQ) (a : ℝ)
    (hcore : ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (C : ℝ≥0),
      LipschitzWith C v → HasCompactSupport v → tsupport v ⊆ Ω →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v → (∀ x, 0 ≤ v x) →
      energyForm μ hQ u ψ ≤ a*inner ℝ (SobolevSpace.toLp μ hQ u) (SobolevSpace.toLp μ hQ ψ)) :
    IsWeakSubsolutionOn μ hQ Ω u a := by
  intro φ hφ
  let pos : ℝ → ℝ := fun t => max t 0
  have hp : LipschitzWith 1 pos :=
    (LipschitzWith.id : LipschitzWith 1 (fun t : ℝ => t)).max_const 0
  have hp0 : pos 0 = 0 := max_self 0
  obtain ⟨fs,hfs,hlim⟩ := mem_closure_iff_seq_limit.mp φ.property
  obtain ⟨D,hD⟩ := (Metric.isBounded_range_of_tendsto fs hlim).exists_norm_le
  let T := fun i => SobolevSpace.compContraction μ hQ hp hp0 (fs i)
  have hTb (i : ℕ) : ‖T i‖ ≤ D :=
    (SobolevSpace.norm_compContraction_le μ hQ hp hp0 (fs i)).trans (hD (fs i) (mem_range_self i))
  have hclip : hp.compLp hp0 (SobolevSpace.toLp μ hQ φ.val) = SobolevSpace.toLp μ hQ φ.val := by
    apply Lp.ext
    filter_upwards [hp.coeFn_compLp hp0 (SobolevSpace.toLp μ hQ φ.val),hφ] with x hx hb
    rw [hx]
    exact max_eq_left hb
  have hTl : Tendsto (fun i => SobolevSpace.toLp μ hQ (T i)) atTop
      (𝓝 (SobolevSpace.toLp μ hQ φ.val)) := by
    have ht := (hp.continuous_compLp hp0).continuousAt.tendsto.comp
      ((SobolevSpace.toLpCLM μ hQ).continuous.continuousAt.tendsto.comp hlim)
    change Tendsto (fun i => hp.compLp hp0 (SobolevSpace.toLp μ hQ (fs i))) atTop
      (𝓝 (hp.compLp hp0 (SobolevSpace.toLp μ hQ φ.val))) at ht
    rwa [hclip] at ht
  have hE := SobolevSpace.energyForm_tendsto_of_toLp_tendsto_bounded μ hQ hTb hTl u
  have hI : Tendsto (fun i => a*inner ℝ (SobolevSpace.toLp μ hQ u)
      (SobolevSpace.toLp μ hQ (T i))) atTop
      (𝓝 (a*inner ℝ (SobolevSpace.toLp μ hQ u) (SobolevSpace.toLp μ hQ φ.val))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.inner hTl)
  rw [energyForm_comm μ hQ u φ.val]
  apply le_of_tendsto_of_tendsto hE hI
  apply Eventually.of_forall
  intro i
  change energyForm μ hQ (T i) u ≤ a*inner ℝ (SobolevSpace.toLp μ hQ u)
    (SobolevSpace.toLp μ hQ (T i))
  rw [energyForm_comm μ hQ (T i) u]
  obtain ⟨g,C,hg,hgc,hgs,hfg⟩ := hfs i
  exact hcore (T i) (pos ∘ g) C (by simpa only [one_mul] using! hp.comp hg)
    (hgc.comp_left hp0) ((tsupport_comp_subset hp0 g).trans hgs)
    ((hp.coeFn_compLp hp0 (SobolevSpace.toLp μ hQ (fs i))).trans (hfg.fun_comp pos))
    (fun x => le_max_right _ _)

end RegularPointCoordinates

end

end OAI
