import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearMetricChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ContinuousFlowDistortion
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic

namespace OAI

/-!
# Removing the additive error from a vector-valued homomorphism

A homomorphism to a real normed vector group scales exactly on powers.
Distances in a left-invariant source metric grow at most linearly on powers.
Consequently an affine upper bound for the homomorphism is already a genuine
Lipschitz bound. Compactness and the existing linear-chain argument supply
the affine bound for continuous homomorphisms.
-/

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The additive constant disappears by applying the bound to arbitrarily
large powers. No commutativity of the source is required. -/
theorem height_lipschitz_of_affine_bound (π : G →* Multiplicative W)
    {K C : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ g, ‖(π g).toAdd‖ ≤ K * dist (1 : G) g + C) :
    ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y := by
  have hone (g : G) : ‖(π g).toAdd‖ ≤ K * dist (1 : G) g := by
    by_contra h
    have hpos : 0 < ‖(π g).toAdd‖ - K * dist (1 : G) g :=
      sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨n, hn⟩ := exists_nat_gt (C / (‖(π g).toAdd‖ - K * dist (1 : G) g))
    have hlarge : C < (n : ℝ) * (‖(π g).toAdd‖ - K * dist (1 : G) g) :=
      (div_lt_iff₀ hpos).mp hn
    have hp : ‖(π (g ^ n)).toAdd‖ = (n : ℝ) * ‖(π g).toAdd‖ := by
      rw [map_pow, toAdd_pow, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
      simp
    have hb := hbound (g ^ n)
    have hd := mul_le_mul_of_nonneg_left (dist_one_pow_le g n) hK
    rw [hp] at hb
    nlinarith
  intro x y
  have h := hone (x⁻¹ * y)
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, dist_one_groupDifference] at h
  simpa only [← sub_eq_add_neg, add_comm (-(π x).toAdd), norm_sub_rev] using h

/-- A continuous vector-valued homomorphism from a proper group with linear
metric chains is globally Lipschitz. -/
theorem continuous_height_lipschitz [ProperSpace G] (C : LinearMetricChains G)
    (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y := by
  obtain ⟨K, B, hK, _, hbound⟩ := continuousHom_coarseLipschitz C π hπ
  refine ⟨K, hK, height_lipschitz_of_affine_bound π (C := B) hK (fun g => ?_)⟩
  have h := hbound 1 g
  rw [map_one] at h
  change dist (0 : W) (π g).toAdd ≤ K * dist (1 : G) g + B at h
  simpa only [dist_zero_left] using h

end PolycyclicRecognition

end OAI
