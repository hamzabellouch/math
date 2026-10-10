import OAI.Geometry.IsometricImmersion.Curvature.GaussFormula
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Calculus.ContDiff.WithLp

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open WithLp

namespace SmoothLocal.Geometry

def ambientCross (u v : Ambient) : Ambient :=
  toLp 2 (crossProduct (ofLp u) (ofLp v))

theorem ambientCross_inner_left (u v : Ambient) : inner ℝ u (ambientCross u v) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change crossProduct (ofLp u) (ofLp v) ⬝ᵥ star (ofLp u) = 0
  rw [star_trivial, dotProduct_comm, dot_self_cross]

theorem ambientCross_inner_right (u v : Ambient) : inner ℝ v (ambientCross u v) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change crossProduct (ofLp u) (ofLp v) ⬝ᵥ star (ofLp v) = 0
  rw [star_trivial, dotProduct_comm, dot_cross_self]

theorem ambientCross_ne_zero_of_independent (t : Fin 2 → Ambient)
    (ht : LinearIndependent ℝ t) : ambientCross (t 0) (t 1) ≠ 0 := by
  let e : Ambient ≃ₗ[ℝ] (Fin 3 → ℝ) := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  have hm : LinearIndependent ℝ (fun i => e (t i)) := by
    exact ht.map' e.toLinearMap (LinearMap.ker_eq_bot_of_injective e.injective)
  have heq : (fun i => e (t i)) = ![ofLp (t 0), ofLp (t 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at hm
  have hc := crossProduct_ne_zero_iff_linearIndependent.mpr hm
  simpa only [ambientCross, ne_eq, WithLp.toLp_eq_zero] using hc

theorem ambientCross_contDiffOn {a b : Coord → Ambient} {U : Set Coord}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (fun p => ambientCross (a p) (b p)) U := by
  have ha' := (contDiffOn_piLp 2).mp ha
  have hb' := (contDiffOn_piLp 2).mp hb
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiffOn ℝ ∞ (fun p => a p 1 * b p 2 - a p 2 * b p 1) U
    exact ((ha' 1).mul (hb' 2)).sub ((ha' 2).mul (hb' 1))
  · change ContDiffOn ℝ ∞ (fun p => a p 2 * b p 0 - a p 0 * b p 2) U
    exact ((ha' 2).mul (hb' 0)).sub ((ha' 0).mul (hb' 2))
  · change ContDiffOn ℝ ∞ (fun p => a p 0 * b p 1 - a p 1 * b p 0) U
    exact ((ha' 0).mul (hb' 1)).sub ((ha' 1).mul (hb' 0))

def tangentCross (F : Coord → Ambient) (p : Coord) : Ambient :=
  ambientCross (coordPartial 0 F p) (coordPartial 1 F p)

def unitNormalField (F : Coord → Ambient) (p : Coord) : Ambient :=
  ‖tangentCross F p‖⁻¹ • tangentCross F p

variable {g : MetricField} {F : Coord → Ambient} {U : Set Coord} {p : Coord}

theorem tangentCross_ne_zero (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hp : p ∈ U) : tangentCross F p ≠ 0 :=
  ambientCross_ne_zero_of_independent (fun i => coordPartial i F p)
    (isometric_tangents_independent hg hF hp)

theorem tangentCross_contDiffOn (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (tangentCross F) U :=
  ambientCross_contDiffOn (partial_contDiffOn hF hU 0) (partial_contDiffOn hF hU 1)

theorem unitNormalField_norm (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hp : p ∈ U) : ‖unitNormalField F p‖ = 1 :=
  norm_smul_inv_norm (𝕜 := ℝ) (tangentCross_ne_zero hg hF hp)

theorem unitNormalField_inner_self (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hp : p ∈ U) : inner ℝ (unitNormalField F p) (unitNormalField F p) = 1 := by
  rw [real_inner_self_eq_norm_sq, unitNormalField_norm hg hF hp, one_pow]

theorem unitNormalField_inner_coordPartial (F : Coord → Ambient) (p : Coord) (i : Fin 2) :
    inner ℝ (coordPartial i F p) (unitNormalField F p) = 0 := by
  fin_cases i
  · rw [unitNormalField, real_inner_smul_right]
    change ‖tangentCross F p‖⁻¹ *
      inner ℝ (coordPartial 0 F p) (ambientCross (coordPartial 0 F p) (coordPartial 1 F p)) = 0
    rw [ambientCross_inner_left, mul_zero]
  · rw [unitNormalField, real_inner_smul_right]
    change ‖tangentCross F p‖⁻¹ *
      inner ℝ (coordPartial 1 F p) (ambientCross (coordPartial 0 F p) (coordPartial 1 F p)) = 0
    rw [ambientCross_inner_right, mul_zero]

theorem unitNormalField_isUnitNormalAt (hg : SmoothPositiveOn g U)
    (hF : IsometricOn g F U) (hp : p ∈ U) :
    IsUnitNormalAt F (unitNormalField F p) p := by
  refine ⟨unitNormalField_inner_self hg hF hp, ?_⟩
  intro v
  rw [← Finset.univ_sum_single v, map_sum, sum_inner]
  apply Finset.sum_eq_zero
  intro i _
  have hsingle : Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
    ext j
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hsingle, map_smul, real_inner_smul_left]
  change v i * inner ℝ (coordPartial i F p) (unitNormalField F p) = 0
  rw [unitNormalField_inner_coordPartial, mul_zero]

theorem unitNormalField_contDiffOn (hg : SmoothPositiveOn g U)
    (hF : IsometricOn g F U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (unitNormalField F) U := by
  have hc := tangentCross_contDiffOn hF.1 hU
  have hn := hc.norm ℝ (fun p hp => tangentCross_ne_zero hg hF hp)
  exact (hn.inv (fun p hp => norm_ne_zero_iff.mpr (tangentCross_ne_zero hg hF hp))).smul hc

theorem exists_smooth_unitNormalField (hg : SmoothPositiveOn g U)
    (hF : IsometricOn g F U) (hU : IsOpen U) :
    ∃ n : Coord → Ambient, ContDiffOn ℝ ∞ n U ∧
      ∀ p ∈ U, IsUnitNormalAt F (n p) p :=
  ⟨unitNormalField F, unitNormalField_contDiffOn hg hF hU,
    fun p hp => unitNormalField_isUnitNormalAt (p := p) hg hF hp⟩

end SmoothLocal.Geometry

end

end OAI
