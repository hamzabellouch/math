import OAI.GroupTheory.PolycyclicRecognition.Geometry.PublishedRootDistortion
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportLegs
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! # Averaged homomorphisms vanish on logarithmically distorted flows

A continuous homomorphism is linear on each one-parameter subgroup. A
linear metric bound and logarithmic distortion force that linear value to
vanish. In particular, the stationary mean kills the actual root flows.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter LieAlgebra LieModule
open scoped Topology Manifold

section Flow

variable {G W : Type*} [Group G] [PseudoMetricSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The image of a continuous one-parameter subgroup under a continuous
homomorphism is a real-linear one-parameter subgroup. -/
theorem hom_flow_eq_smul
    (d : ℝ → G) (hd : Continuous d) (hd₀ : d 0 = 1)
    (hdadd : ∀ s t, d (s + t) = d s * d t)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd) (t : ℝ) :
    (l (d t)).toAdd = t • (l (d 1)).toAdd := by
  let a : ℝ →+ W := {
    toFun t := (l (d t)).toAdd
    map_zero' := by rw [hd₀, map_one]; rfl
    map_add' := fun s t => by rw [hdadd, map_mul]; rfl }
  have ha : Continuous a := hl.comp hd
  have h := (a.toRealLinearMap ha).map_smul t (1 : ℝ)
  change a t = t • a 1
  change a (t • (1 : ℝ)) = t • a 1 at h
  simpa only [smul_eq_mul, mul_one] using h

/-- Linear metric control precludes a nonzero homomorphism on a flow of
logarithmic ambient size. -/
theorem hom_eq_one_of_logarithmic_flow
    (d : ℝ → G) (hd : Continuous d) (hd₀ : d 0 = 1)
    (hdadd : ∀ s t, d (s + t) = d s * d t)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L D B : ℝ} (hL : 0 ≤ L) (hB : 0 < B)
    (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (hdist : ∀ t, dist 1 (d t) ≤ D * Real.log (2 + B * |t|)) :
    ∀ t, l (d t) = 1 := by
  have hscale := hom_flow_eq_smul d hd hd₀ hdadd l hl
  have hat : Tendsto (fun t : ℝ => 2 + B * t) atTop atTop := by
    apply tendsto_atTop.mpr
    intro x
    filter_upwards [eventually_ge_atTop ((x - 2) / B)] with t ht
    have hh := (div_le_iff₀ hB).mp ht
    nlinarith
  have hden (t : ℝ) : (1 / B) * (2 + B * t) + (-2 / B) = t := by
    field_simp
    ring
  have hlim : Tendsto (fun t : ℝ => L * D * Real.log (2 + B * t) / t) atTop (𝓝 0) := by
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop (1 / B) (-2 / B) 1
      (one_div_ne_zero hB.ne')).comp hat
    change Tendsto (fun t : ℝ => Real.log (2 + B * t) ^ 1 /
      ((1 / B) * (2 + B * t) + (-2 / B))) atTop (𝓝 0) at hh
    simp only [pow_one, hden] at hh
    simpa only [mul_zero, mul_div_assoc] using hh.const_mul (L * D)
  have hle : ∀ᶠ t : ℝ in atTop,
      ‖(l (d 1)).toAdd‖ ≤ L * D * Real.log (2 + B * t) / t := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hb := (hbound (d t)).trans (mul_le_mul_of_nonneg_left (hdist t) hL)
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hb
    apply (le_div_iff₀ ht0).mpr
    nlinarith
  have hz : (l (d 1)).toAdd = 0 := norm_eq_zero.mp
    (le_antisymm (ge_of_tendsto hlim hle) (norm_nonneg _))
  intro t
  change (l (d t)).toAdd = 0
  rw [hscale, hz, smul_zero]

end Flow

variable {G W EG : Type*} [Group G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- Every continuous homomorphism with linear metric control kills the
root exponentials, using their logarithmic distortion. -/
theorem hom_eq_one_on_root_exp
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : LieModule.Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (v : rootSpace H χ) :
    ∀ t : ℝ, l (Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))) = 1 := by
  obtain ⟨D, hD, hb⟩ := root_distortion_of_published_realization T H χ hχ Exp hExp realize
  let B := 1 + ‖rootCoordinates H χ v‖
  have hB : 0 < B := by dsimp [B]; positivity
  apply hom_eq_one_of_logarithmic_flow
    (fun t : ℝ => Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (continuous_exp_line_of_published_realization T Exp hExp realize v)
    (by simp [hExp.map_zero])
    (fun s t => hExp.map_add_smul v s t) l hl hL hB hbound
  intro t
  have h := hb (t • v)
  have hn : 2 + ‖rootCoordinates H χ (t • v)‖ ≤ 2 + B * |t| := by
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    dsimp [B]
    nlinarith [abs_nonneg t]
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.log_le_log (by positivity) hn) hD.le)

end PolycyclicRecognition

end

end OAI
