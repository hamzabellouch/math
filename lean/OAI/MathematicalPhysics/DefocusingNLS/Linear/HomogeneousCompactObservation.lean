import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEvaluationContinuity
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Normed.Operator.Compact.Basic

namespace OAI

/-! # Compact local observation of the faithful homogeneous space

Restricting the actual inverse Fourier function to a compact spatial set is
a compact linear operator. Norm-continuity of the point evaluations provides
the equicontinuity required by Arzelà–Ascoli.
-/

open Set Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousLocalObservation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (S : Set E) :
    HomogeneousY a k →L[ℂ] (S →ᵇ ℂ) :=
  ({ toFun := fun f => (homogeneousPhysicalCLM a k ha ha1 hk f).toBCF.compContinuous
        ⟨Subtype.val, continuous_subtype_val⟩
     map_add' := by
       intro f g
       apply BoundedContinuousFunction.ext
       intro x
       change homogeneousPhysicalCLM a k ha ha1 hk (f + g) x =
         homogeneousPhysicalCLM a k ha ha1 hk f x + homogeneousPhysicalCLM a k ha ha1 hk g x
       simp only [map_add, ZeroAtInftyContinuousMap.add_apply]
     map_smul' := by
       intro c f
       apply BoundedContinuousFunction.ext
       intro x
       change homogeneousPhysicalCLM a k ha ha1 hk (c • f) x =
         c • homogeneousPhysicalCLM a k ha ha1 hk f x
       simp only [map_smul, ZeroAtInftyContinuousMap.smul_apply] } :
    HomogeneousY a k →ₗ[ℂ] (S →ᵇ ℂ)).mkContinuous
      ‖homogeneousPhysicalCLM a k ha ha1 hk‖ (by
        intro f
        exact (BoundedContinuousFunction.norm_compContinuous_le _ _).trans
          ((homogeneousPhysicalCLM a k ha ha1 hk).le_opNorm f))

@[simp] theorem homogeneousLocalObservation_apply (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (S : Set E)
    (f : HomogeneousY a k) (x : S) :
    homogeneousLocalObservation a k ha ha1 hk S f x =
      homogeneousPhysicalCLM a k ha ha1 hk f x := rfl

theorem isCompact_homogeneousLocalObservation_unitBall (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (S : Set E) [CompactSpace S] :
    IsCompact (closure (homogeneousLocalObservation a k ha ha1 hk S ''
      Metric.closedBall 0 1)) := by
  let T := homogeneousLocalObservation a k ha ha1 hk S
  let A : Set (S →ᵇ ℂ) := T '' Metric.closedBall 0 1
  let c := ‖homogeneousPointEvaluation a k ha ha1 hk 0‖
  have hrange : ∀ (f : S →ᵇ ℂ) (x : S), f ∈ A → f x ∈ Metric.closedBall 0 c := by
    intro f x hf
    rcases hf with ⟨v, hv, rfl⟩
    have hvnorm : ‖v‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖homogeneousPointEvaluation a k ha ha1 hk x v‖ ≤ c
    calc
      _ ≤ ‖homogeneousPointEvaluation a k ha ha1 hk x‖ * ‖v‖ :=
        (homogeneousPointEvaluation a k ha ha1 hk x).le_opNorm v
      _ ≤ ‖homogeneousPointEvaluation a k ha ha1 hk x‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hvnorm
      _ = c := homogeneousPointEvaluation_norm_const a k ha ha1 hk x
  have hequi : Equicontinuous ((↑) : A → S → ℂ) := by
    intro x₀
    apply Metric.equicontinuousAt_iff_right.mpr
    intro ε hε
    have hc := ((continuous_homogeneousPointEvaluation a k ha ha1 hk).comp
      continuous_subtype_val).continuousAt (x := x₀)
    have hevent : ∀ᶠ x : S in 𝓝 x₀,
        dist (homogeneousPointEvaluation a k ha ha1 hk x₀)
          (homogeneousPointEvaluation a k ha ha1 hk x) < ε := by
      simpa only [Metric.mem_ball, dist_comm, Function.comp_def] using
        hc.eventually (Metric.ball_mem_nhds _ hε)
    filter_upwards [hevent] with x hx
    intro f
    rcases f.property with ⟨v, hv, hvf⟩
    have hvnorm : ‖v‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    change dist (f.val x₀) (f.val x) < ε
    rw [← hvf, dist_eq_norm]
    change ‖(homogeneousPointEvaluation a k ha ha1 hk x₀ -
      homogeneousPointEvaluation a k ha ha1 hk x) v‖ < ε
    calc
      _ ≤ ‖homogeneousPointEvaluation a k ha ha1 hk x₀ -
          homogeneousPointEvaluation a k ha ha1 hk x‖ * ‖v‖ :=
        (homogeneousPointEvaluation a k ha ha1 hk x₀ -
          homogeneousPointEvaluation a k ha ha1 hk x).le_opNorm v
      _ ≤ ‖homogeneousPointEvaluation a k ha ha1 hk x₀ -
          homogeneousPointEvaluation a k ha ha1 hk x‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hvnorm
      _ < ε := by simpa only [dist_eq_norm] using hx
  exact BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 c)
    (isCompact_closedBall 0 c) A hrange hequi

theorem isCompactOperator_homogeneousLocalObservation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (S : Set E) [CompactSpace S] :
    IsCompactOperator (homogeneousLocalObservation a k ha ha1 hk S) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (homogeneousLocalObservation a k ha ha1 hk S).toLinearMap zero_lt_one).mpr
  exact isCompact_homogeneousLocalObservation_unitBall a k ha ha1 hk S

end DefocusingNLS

end OAI
