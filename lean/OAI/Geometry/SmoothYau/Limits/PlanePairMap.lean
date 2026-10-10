import Mathlib

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def planePairMap (a b : V) : (ℝ × ℝ) →ₗ[ℝ] V where
  toFun c := c.1 • a + c.2 • b
  map_add' c d := by simp [add_smul]; abel
  map_smul' r c := by simp [smul_add, smul_smul]

def tangentProjection (p : V) : V →ₗ[ℝ] V :=
  LinearMap.id - (innerSL ℝ p).toLinearMap.smulRight p

@[simp] lemma tangentProjection_apply (p v : V) :
    tangentProjection p v = v - inner ℝ p v • p := rfl

@[simp] lemma planePairMap_apply (a b : V) (s t : ℝ) :
    planePairMap a b (s,t) = s • a + t • b := rfl

def projectedPlaneMap (p a b : V) : (ℝ × ℝ) →ₗ[ℝ] V :=
  (tangentProjection p).comp (planePairMap a b)

lemma projectedPlaneMap_tangent (p a b : V) (hp : inner ℝ p p = 1) (c : ℝ × ℝ) :
    inner ℝ p (projectedPlaneMap p a b c) = 0 := by
  simp only [projectedPlaneMap, LinearMap.comp_apply, tangentProjection_apply,
    inner_sub_right, inner_smul_right, hp, mul_one, sub_self]

lemma projectedPlaneMap_norm_sq (p a b : V) (hp : inner ℝ p p = 1)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (c : ℝ × ℝ) :
    inner ℝ (projectedPlaneMap p a b c) (projectedPlaneMap p a b c) =
      c.1^2 + c.2^2 - (c.1 * inner ℝ p a + c.2 * inner ℝ p b)^2 := by
  simp only [projectedPlaneMap, LinearMap.comp_apply, tangentProjection_apply,
    planePairMap, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, inner_smul_right, hp, ha, hb, hab,
    show inner ℝ b a = 0 from (real_inner_comm a b).trans hab,
    real_inner_comm a p, real_inner_comm b p]
  ring

lemma projectedPlaneMap_quadratic (p a b : V) (hp : inner ℝ p p = 1)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (c : ℝ × ℝ) :
    (inner ℝ a (projectedPlaneMap p a b c))^2 +
        (inner ℝ b (projectedPlaneMap p a b c))^2 =
      c.1^2+c.2^2 - (2-((inner ℝ p a)^2+(inner ℝ p b)^2))*
        (c.1*inner ℝ p a+c.2*inner ℝ p b)^2 := by
  calc
    _ = inner ℝ (projectedPlaneMap p a b c) (projectedPlaneMap p a b c) -
        (1-((inner ℝ p a)^2+(inner ℝ p b)^2))*
          (c.1*inner ℝ p a+c.2*inner ℝ p b)^2 := by
      simp only [projectedPlaneMap, LinearMap.comp_apply, tangentProjection_apply,
        planePairMap, LinearMap.coe_mk, AddHom.coe_mk,
        inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
        real_inner_smul_left, inner_smul_right, hp, ha, hb, hab,
        show inner ℝ b a = 0 from (real_inner_comm a b).trans hab,
        real_inner_comm a p, real_inner_comm b p]
      ring
    _ = _ := by
      rw [projectedPlaneMap_norm_sq p a b hp ha hb hab]
      ring

lemma plane_cauchy (A B s t : ℝ) :
    (s*A+t*B)^2 ≤ (A^2+B^2)*(s^2+t^2) := by
  nlinarith [sq_nonneg (s*B-t*A)]

lemma projectedPlaneMap_lower (p a b : V) (hp : inner ℝ p p = 1)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (c : ℝ × ℝ) :
    (1-((inner ℝ p a)^2+(inner ℝ p b)^2))*(c.1^2+c.2^2) ≤
      inner ℝ (projectedPlaneMap p a b c) (projectedPlaneMap p a b c) := by
  rw [projectedPlaneMap_norm_sq p a b hp ha hb hab]
  nlinarith [plane_cauchy (inner ℝ p a) (inner ℝ p b) c.1 c.2]

lemma projectedPlaneMap_injective (p a b : V) (hp : inner ℝ p p = 1)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (hr : (inner ℝ p a)^2+(inner ℝ p b)^2 < 1) :
    Function.Injective (projectedPlaneMap p a b) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro c hc
  have hz : projectedPlaneMap p a b c = 0 := hc
  have hh := projectedPlaneMap_lower p a b hp ha hb hab c
  rw [hz, inner_zero_left] at hh
  have hq : c.1^2+c.2^2 = 0 := by
    nlinarith [sq_nonneg c.1, sq_nonneg c.2]
  have h₁ : c.1 = 0 := by nlinarith [sq_nonneg c.2]
  have h₂ : c.2 = 0 := by nlinarith [sq_nonneg c.1]
  exact Prod.ext h₁ h₂

lemma projectedPlaneMap_quadratic_lower (p a b : V) (hp : inner ℝ p p = 1)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (c : ℝ × ℝ) :
    (1-((inner ℝ p a)^2+(inner ℝ p b)^2))*
        inner ℝ (projectedPlaneMap p a b c) (projectedPlaneMap p a b c) ≤
      (inner ℝ a (projectedPlaneMap p a b c))^2 +
        (inner ℝ b (projectedPlaneMap p a b c))^2 := by
  rw [projectedPlaneMap_quadratic p a b hp ha hb hab,
    projectedPlaneMap_norm_sq p a b hp ha hb hab]
  nlinarith [plane_cauchy (inner ℝ p a) (inner ℝ p b) c.1 c.2]

end YauCounterexamples

end

end OAI
