import Mathlib
import OAI.Geometry.NearbyLagrangian.MomentumSeparation
import OAI.Geometry.NearbyLagrangian.RealizationRegularity

namespace OAI

/-! Injectivity of the realization from exact momentum coefficients. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.EmbeddedRealization

open scoped Manifold ContDiff InnerProductSpace Topology
open Tubes Tubes.RegularHomogeneous CoreSmoothing Cutoff Scales
open Set Filter

variable {W E B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace B] [ChartedSpace E B] [IsManifold 𝓘(ℝ, E) ∞ B]
  {n : ℕ} [Fact (Module.finrank ℝ W = n + 1)]

local instance realizationInjectivityChartedSpace : ChartedSpace (E × EuclideanSpace ℝ (Fin n))
    (B × Metric.sphere (0 : W) 1) :=
  inferInstanceAs (ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin n)))
    (B × Metric.sphere (0 : W) 1))

local instance realizationInjectivityManifold : IsManifold 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) ∞
    (B × Metric.sphere (0 : W) 1) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, E)) (I' := 𝓡 n) B (Metric.sphere (0 : W) 1)

def cotangentCoefficient (z : CotangentGeometry.Cotangent
    (E := E × EuclideanSpace ℝ (Fin n)) (M := B × Metric.sphere (0 : W) 1)) :
    (E × EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ := z.2

omit [IsManifold 𝓘(ℝ, E) ∞ B] in

theorem sourceGeneratingMap_coefficient {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ}
    (hRs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ R) {T c C : ℝ}
    (hT : 0 < T) (hc : 0 < c) (hR : ∀ b, 0 < R b) (hC : ∀ b, C < R b)
    (hscale : ∀ b, R b / c < T)
    (hlower : ∀ b w, c * ‖w‖ ≤ ‖gradient (f b) w‖)
    (hupper : ∀ b w, ‖gradient (f b) w‖ ≤ C * ‖w‖)
    (b : B) (u : Metric.sphere (0 : W) 1)
    (a : E)
    (d : EuclideanSpace ℝ (Fin n)) :
    cotangentCoefficient (sourceGeneratingMap (E := E) (n := n) f R T (b, u)) (a, d) =
      (MixedDerivative.baseDerivative (E := E) (fun b w => f b w) b
        ((f b).radialSolution (R b) u)) a -
      (mvfderiv 𝓘(ℝ, E) R b a : ℝ) *
        ⟪(f b).radialSolution (R b) u, ((f b).direction u : W)⟫_ℝ -
      R b * ⟪(f b).radialSolution (R b) u,
        mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W) ((f b).direction u) d⟫_ℝ := by
  let w := (f b).radialSolution (R b) u
  obtain ⟨hw₁, hwT⟩ := critical_annulus hc b (hR b) (hC b) (hscale b)
    (hlower b) (hupper b) ((f b).direction u) w ((f b).radialSolution_critical (R b) (hR b) u)
  have heq : (fun q : B × Metric.sphere (0 : W) 1 => sourceFamily f R T (q, w)) =
      (fun q => f q.1 w - R q.1 * ⟪w, (q.2 : W)⟫_ℝ) := by
    funext q
    rw [sourceFamily_eq_uncut hT q.1 q.2 w hw₁.le hwT.le, real_inner_comm]
  have hfb : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun t => f t w) b := by
    have hh := (hf (b, w) (by exact (f b).radialSolution_ne_zero (R b) (hR b) u)).comp b
      (contMDiffAt_id.prodMk contMDiffAt_const)
    exact hh.mdifferentiableAt (by simp)
  change mfderiv 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ)
    (fun q => sourceFamily f R T (q, w)) (b, (f b).direction u) (a, d) = _
  rw [modelWithCornersSelf_prod, heq]
  exact MomentumCalculus.uncut_mfderiv hfb ((hRs b).mdifferentiableAt (by simp))
    w ((f b).direction u) a d

omit [IsManifold 𝓘(ℝ, E) ∞ B] in

theorem sourceGeneratingMap_injective {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ}
    (hRs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ R) {T c C : ℝ}
    (hT : 0 < T) (hc : 0 < c) (hR : ∀ b, 0 < R b) (hC : ∀ b, C < R b)
    (hscale : ∀ b, R b / c < T)
    (hlower : ∀ b w, c * ‖w‖ ≤ ‖gradient (f b) w‖)
    (hupper : ∀ b w, ‖gradient (f b) w‖ ≤ C * ‖w‖)
    (hsep : ∀ b, Function.Injective (gradient (f b)) ∨
      ∃ (a : E) (C₁ : ℝ), 0 ≤ C₁ ∧
        Differentiable ℝ (fun w => MixedDerivative.baseDerivative (E := E)
          (fun b w => f b w) b w a) ∧
        (∀ w, ‖fderiv ℝ (fun z => MixedDerivative.baseDerivative (E := E)
          (fun b w => f b w) b z a) w‖ ≤ C₁ * ‖w‖) ∧
        C₁ * (R b / c) < |(mvfderiv 𝓘(ℝ, E) R b a : ℝ)|) :
    Function.Injective (sourceGeneratingMap (E := E) (n := n) f R T) := by
  rintro ⟨b, u⟩ ⟨b', u'⟩ heq
  have hb : b = b' := congrArg (fun z => z.proj.1) heq
  subst b'
  have hv : (f b).direction u = (f b).direction u' := congrArg (fun z => z.proj.2) heq
  have hm := congrArg (cotangentCoefficient (E := E) (n := n)) heq
  let w := (f b).radialSolution (R b) u
  let w' := (f b).radialSolution (R b) u'
  let DR : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) R b
  have hcrit : gradient (f b) w = R b • ((f b).direction u : W) :=
    (f b).radialSolution_critical (R b) (hR b) u
  have hcrit' : gradient (f b) w' = R b • ((f b).direction u' : W) :=
    (f b).radialSolution_critical (R b) (hR b) u'
  have hnorm : ‖w‖ ≤ R b / c := by
    apply (le_div_iff₀ hc).mpr
    have hh := hlower b w
    rw [hcrit, norm_smul, Real.norm_eq_abs, abs_of_pos (hR b),
      norm_eq_of_mem_sphere, mul_one] at hh
    nlinarith
  have hnorm' : ‖w'‖ ≤ R b / c := by
    apply (le_div_iff₀ hc).mpr
    have hh := hlower b w'
    rw [hcrit', norm_smul, Real.norm_eq_abs, abs_of_pos (hR b),
      norm_eq_of_mem_sphere, mul_one] at hh
    nlinarith
  have hw : w = w' := by
    rcases hsep b with hquadratic | ⟨a, C₁, hC₁, hP, hDP, hdom⟩
    · apply hquadratic
      rw [hcrit, hcrit', hv]
    · have hsphere : ∀ d : EuclideanSpace ℝ (Fin n),
          ⟪w, mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W) ((f b).direction u) d⟫_ℝ =
          ⟪w', mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W) ((f b).direction u) d⟫_ℝ := by
        intro d
        have hd := congrArg (fun L => L (0, d)) hm
        erw [sourceGeneratingMap_coefficient hf hRs hT hc hR hC hscale hlower hupper,
          sourceGeneratingMap_coefficient hf hRs hT hc hR hC hscale hlower hupper] at hd
        change MixedDerivative.baseDerivative (E := E) (fun b w => f b w) b w 0 -
          DR 0 * ⟪w, ((f b).direction u : W)⟫_ℝ -
          R b * ⟪w, mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W)
            ((f b).direction u) d⟫_ℝ =
          MixedDerivative.baseDerivative (E := E) (fun b w => f b w) b w' 0 -
          DR 0 * ⟪w', ((f b).direction u' : W)⟫_ℝ -
          R b * ⟪w', mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W)
            ((f b).direction u') d⟫_ℝ at hd
        simp only [_root_.map_zero, zero_mul, zero_sub, neg_zero] at hd
        rw [hv] at hd ⊢
        exact (mul_left_cancel₀ (hR b).ne') (neg_injective hd)
      have hbase :
          MixedDerivative.baseDerivative (E := E) (fun b w => f b w) b w a -
            ⟪((f b).direction u : W), w⟫_ℝ * DR a =
          MixedDerivative.baseDerivative (E := E) (fun b w => f b w) b w' a -
            ⟪((f b).direction u : W), w'⟫_ℝ * DR a := by
        have hd := congrArg (fun L => L (a, 0)) hm
        erw [sourceGeneratingMap_coefficient hf hRs hT hc hR hC hscale hlower hupper,
          sourceGeneratingMap_coefficient hf hRs hT hc hR hC hscale hlower hupper] at hd
        let DS : EuclideanSpace ℝ (Fin n) →L[ℝ] W :=
          mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W) ((f b).direction u)
        let DS' : EuclideanSpace ℝ (Fin n) →L[ℝ] W :=
          mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W) ((f b).direction u')
        change MixedDerivative.baseDerivative (E := E) (fun b w => f b w) b w a -
          DR a * ⟪w, ((f b).direction u : W)⟫_ℝ - R b * ⟪w, DS 0⟫_ℝ =
          MixedDerivative.baseDerivative (E := E) (fun b w => f b w) b w' a -
          DR a * ⟪w', ((f b).direction u' : W)⟫_ℝ - R b * ⟪w', DS' 0⟫_ℝ at hd
        simp only [_root_.map_zero, inner_zero_right, mul_zero, sub_zero] at hd
        rw [hv] at hd ⊢
        simpa only [real_inner_comm, mul_comm] using hd
      exact BranchSeparation.eq_of_equal_base_momenta hP hC₁ hDP
        (norm_eq_of_mem_sphere ((f b).direction u)) hnorm hnorm' hdom
        (BranchSeparation.sub_mem_radial_of_sphere_momenta ((f b).direction u) hsphere) hbase
  have hu := congrArg (fun z : W => ‖z‖⁻¹ • z) hw
  have h₁ := congrArg Subtype.val ((f b).angularPosition_radialSolution (R b) (hR b) u)
  have h₂ := congrArg Subtype.val ((f b).angularPosition_radialSolution (R b) (hR b) u')
  have huu : (u : W) = (u' : W) := h₁.symm.trans (hu.trans h₂)
  exact congrArg (Prod.mk b) (Subtype.ext huu)

end NearbyLagrangian.EmbeddedRealization

end

end OAI
