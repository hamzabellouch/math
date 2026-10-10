import OAI.Geometry.RCD.Transport.CompressedRadialPlan
import OAI.Geometry.RCD.Transport.RadialPlanSlope
import OAI.Geometry.RCD.Transport.RadialGeodesic

namespace OAI

/-! # The distance eikonal identity from actual RCD transport

Restrict normalized volume to any positive-measure set on which the relaxed
slope is less than one. The constructed compressed radial plan realizes the
full distance speed, contradicting the weak upper gradient inequality.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.inward_minimalSlope_eq_one {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ x ∂(hausdorff n X).restrict (ball p R),
      SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
        (inwardSobolev (hausdorff n X) hX.quadratic p R) x = 1 := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let u := inwardSobolev μ hX.quadratic p R
  let G := SobolevSpace.minimalSlope μ hX.quadratic u
  have hupper : ∀ᵐ x ∂μ, G x ≤ 1 :=
    SobolevSpace.ofLipschitzCompact_minimalSlope_le_lip μ hX.quadratic
      (inwardDistance_lipschitz p R) (inwardDistance_compact p R)
  let A := {x | x ∈ ball p R ∧ x ≠ p ∧ G x < 1}
  have hA : MeasurableSet A := measurableSet_ball.inter
    ((measurableSet_singleton p).compl.inter
      (measurableSet_lt (Lp.stronglyMeasurable G).measurable measurable_const))
  have hAzero : μ A = 0 := by
    by_contra hA0
    have hAtop : μ A ≠ ∞ :=
      ((measure_mono (show A ⊆ ball p R from fun _ hx => hx.1)).trans_lt
        (hX.finiteOnBounded _ isBounded_ball)).ne
    let ν₀ : ProbabilityMeasure X := ⟨uniformOn μ A, uniformOn_probability μ A hA0 hAtop⟩
    have hcap : (μ A)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hA0
    have hbound : (ν₀ : Measure X) ≤ (μ A)⁻¹ • μ := by
      intro S
      exact mul_le_mul_right (Measure.restrict_le_self (μ := μ) (s := A) S) _
    have hs0 : ∀ᵐ x ∂(ν₀ : Measure X), dist x p ≤ R :=
      (uniformOn_ae_mem μ A hA).mono fun _ hx => (mem_ball.mp hx.1).le
    obtain ⟨π, hπ, C, hC, hπ0, hg, hD, hc, hr⟩ :=
      hX.exists_compressed_radial_plan hn ν₀ hcap hbound p hR hs0
    let := hπ
    have ha : ∀ᵐ γ ∂π, γ 0 ∈ A := by
      apply ae_of_ae_map (measurable_path_eval 0).aemeasurable
      rw [hπ0]
      exact uniformOn_ae_mem μ A hA
    have hrep (t : Time) : ∀ᵐ γ ∂π,
        SobolevSpace.toLp μ hX.quadratic u (γ t) = inwardDistance p R (γ t) := by
      apply ae_of_ae_map (measurable_path_eval t).aemeasurable
        (p := fun x => SobolevSpace.toLp μ hX.quadratic u x = inwardDistance p R x)
      exact (Measure.absolutelyContinuous_of_le_smul (hc t)).ae_le
        (inwardSobolev_coe μ hX.quadratic p R)
    have hradial (t : Time) : ∀ᵐ γ ∂π,
        |SobolevSpace.toLp μ hX.quadratic u (γ t) -
          SobolevSpace.toLp μ hX.quadratic u (γ 0)| =
          (t : ℝ) * dist (γ 0) (γ 1) := by
      filter_upwards [hg, hr, ha, hrep t, hrep 0] with γ hgeo hrad hstart ht h0
      rw [ht, h0]
      exact hgeo.inwardDistance_increment (mem_ball.mp hstart.1) hrad.2 t
    have hu : ∀ᵐ γ ∂π, G (γ 0) ≤ 1 := ha.mono fun _ hx => hx.2.2.le
    have hd : ∀ᵐ γ ∂π, 0 < dist (γ 0) (γ 1) := by
      filter_upwards [ha, hr] with γ hstart hrad
      have hp : 0 < dist (γ 0) p := dist_pos.mpr hstart.2.1
      linarith [hrad.1, hrad.2]
    have hone := (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic u).eq_one_of_radial_plan
      μ π hg hC hc hD hradial hu hd
    have hf : ∀ᵐ γ ∂π, False := by
      filter_upwards [ha, hone] with γ hstart heq
      exact (ne_of_lt hstart.2.2) heq
    exact hf.exists.elim fun _ h => h
  have hpzero : μ {p} = 0 := by
    let := Measure.nullSingletonClass_hausdorff X
      (show 0 < (n : ℝ) by exact_mod_cast (show 0 < n by omega))
    simp [μ, hausdorff]
  have hnotA : ∀ᵐ x ∂μ, x ∉ A := by
    apply ae_iff.mpr
    simpa using hAzero
  have hnotp : ∀ᵐ x ∂μ, x ≠ p := by
    apply ae_iff.mpr
    simpa using hpzero
  filter_upwards [ae_restrict_of_ae hupper, ae_restrict_of_ae hnotA,
    ae_restrict_of_ae hnotp, ae_restrict_mem measurableSet_ball] with x hle ha hp hx
  apply le_antisymm hle
  exact le_of_not_gt fun hlt => ha ⟨hx, hp, hlt⟩

theorem NoncollapsedRCD.inwardSobolev_eikonal {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ x ∂(hausdorff n X).restrict (ball p R),
      localGamma (hausdorff n X) hX.quadratic
        (inwardSobolev (hausdorff n X) hX.quadratic p R)
        (inwardSobolev (hausdorff n X) hX.quadratic p R) x = 1 := by
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  filter_upwards [hX.inward_minimalSlope_eq_one hn p hR,
    ae_restrict_of_ae (localGamma_self (hausdorff n X) hX.quadratic
      (inwardSobolev (hausdorff n X) hX.quadratic p R))] with x hx hg
  rw [hg, hx, one_pow]

end RegularPointCoordinates

end

end OAI
