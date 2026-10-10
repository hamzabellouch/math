import Mathlib
import OAI.Geometry.PrescribedRicci.UniformCoefficientExtension
import OAI.Geometry.PrescribedRicci.UniformCoefficientOscillation

namespace OAI

/-! Uniform Path Patches. -/

section

 

noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise BoundedContinuousFunction
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere EllipticKernel FrozenPoisson MetricLocalization SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X}

theorem volumePath_uniform_patch (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A)
    (hd : 2 ≤ d) (q : Fin A.count) (x : EC d) {R : ℝ} (hR : 0 < R)
    (hsub : Metric.closedBall x R ⊆ (A.euclideanChart q).target)
    {ι : Type*} [Fintype ι] (v : ι → EC d) :
    ∃ M r : ℝ, 0 < M ∧ 0 < r ∧ r ≤ R ∧
      ∀ (φ : SmoothRealFunction A) (hp : g.PositivePotential φ), g.integral φ.value = 0 →
      ∀ t b : ℝ, t ∈ Icc (0:ℝ) 1 →
      (∀ y, (g.logRatio (g.deform φ hp)).value y = t*(prescribedForcing g line).value y+b) →
      ‖(g.deform φ hp).matrix q (coordinateEquiv d x)‖ ≤ M ∧
      ∃ a : ι → ι → EC d →ᵇ ℂ,
        (∀ i j, ContDiff ℝ ∞ (a i j : EC d → ℂ)) ∧
        (∀ i j, HasCompactSupport (a i j : EC d → ℂ)) ∧
        perturbationBound v a*uniformEllipticBound d M ≤ 1/2 ∧
        ∀ y ∈ Metric.closedBall x (r/2), ∀ i j,
          a i j y = (traceBilin ((g.deform φ hp).matrix q (coordinateEquiv d y)) (rankTwo (v i) (v j)) : ℂ)-
            (traceBilin ((g.deform φ hp).matrix q (coordinateEquiv d x)) (rankTwo (v i) (v j)) : ℂ) := by
  let K : Set (Coordinates d) := coordinateEquiv d '' Metric.closedBall x R
  have hK : IsCompact K := (isCompact_closedBall x R).image (coordinateEquiv d).continuous
  have hKc : Convex ℝ K := (convex_closedBall x R).linear_image (coordinateEquiv d).toLinearMap
  have hKt : K ⊆ (A.chart q).target := by
    rintro z ⟨y,hy,rfl⟩
    simpa using hsub hy
  have hxK : coordinateEquiv d x ∈ K := ⟨x,Metric.mem_closedBall_self hR.le,rfl⟩
  obtain ⟨M,hM,hmetric⟩ := g.volumePath_metric_bounds_on_compact line hd q hK hKt
  obtain ⟨P,hP,hlip⟩ := g.volumePath_metric_lipschitz_on_compact line hd q hK hKc hKt
  let Q : ℝ := ∑ i, ∑ j, ‖PotentialKaehler.hermitianPartMatrix (pullBilin (rankTwo (v i) (v j)))‖
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hBQ (i j : ι) : ‖PotentialKaehler.hermitianPartMatrix (pullBilin (rankTwo (v i) (v j)))‖ ≤ Q := by
    apply (Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
    exact Finset.single_le_sum (f:=fun i => ∑ j, ‖PotentialKaehler.hermitianPartMatrix (pullBilin (rankTwo (v i) (v j)))‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  let B : ℝ := (d:ℝ)^2*P*‖(coordinateEquiv d).toContinuousLinearMap‖*Q
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨r,hr,hrR,hpatch⟩ := uniform_coefficient_radius v hM.le hB hR
  refine ⟨M,r,hM,hr,hrR,?_⟩
  intro φ hp hm t b ht heq
  refine ⟨(hmetric φ hp hm t b ht heq _ hxK).1,?_⟩
  let H : EC d → Matrix (Fin d) (Fin d) ℂ := fun y => (g.deform φ hp).matrix q (coordinateEquiv d y)
  have hH : ContDiffOn ℝ ∞ H (A.euclideanChart q).target := by
    apply ((g.deform φ hp).smooth q).comp (coordinateEquiv d).contDiff.contDiffOn
    intro y hy
    simpa using hy
  have hh : ∀ y ∈ (A.euclideanChart q).target, (H y).PosDef := by
    intro y hy
    exact (g.deform φ hp).positive q _ (by simpa using hy)
  apply hpatch x (A.euclideanChart q).target (A.euclideanChart q).open_target hsub H hH hh
  intro y hy i j
  have hyK : coordinateEquiv d y ∈ K := ⟨y,hy,rfl⟩
  have hI := (hlip φ hp hm t b ht heq _ hxK _ hyK).2
  have hc : ‖coordinateEquiv d y-coordinateEquiv d x‖ ≤
      ‖(coordinateEquiv d).toContinuousLinearMap‖*‖y-x‖ := by
    rw [← map_sub]
    exact (coordinateEquiv d).toContinuousLinearMap.le_opNorm (y-x)
  have hI' : ‖(H y)⁻¹-(H x)⁻¹‖ ≤ P*‖(coordinateEquiv d).toContinuousLinearMap‖*‖y-x‖ := by
    exact hI.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc hP.le)
  apply (traceBilin_difference_bound (H y) (H x) (rankTwo (v i) (v j))).trans
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hI' (by positivity)) (hBQ i j)
    (norm_nonneg _) (by positivity)).trans_eq
  dsimp only [B]
  ring
end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
