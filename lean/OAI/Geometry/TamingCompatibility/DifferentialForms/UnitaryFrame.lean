import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.JAction

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryFrame

abbrev V := EuclideanSpace ℝ (Fin 4)
abbrev W := EuclideanSpace ℝ (Fin 6)

def J (v : V) : V := WithLp.toLp 2 ![-v 1, v 0, -v 3, v 2]

def wedge (u v : V) : W :=
  WithLp.toLp 2 ![u 0 * v 1 - u 1 * v 0, u 0 * v 2 - u 2 * v 0,
    u 0 * v 3 - u 3 * v 0, u 1 * v 2 - u 2 * v 1,
    u 1 * v 3 - u 3 * v 1, u 2 * v 3 - u 3 * v 2]

def star (a : W) : W := WithLp.toLp 2 ![a 5, -a 4, a 3, a 2, -a 1, a 0]

def fundamental : W := WithLp.toLp 2 ![1, 0, 0, 0, 0, 1]

def line (v : V) : W := wedge v (J v)

def selfDualPart (a : W) : W := (1 / 2 : ℝ) • (a + star a)

lemma J_square (v : V) : J (J v) = -v := by
  ext i
  fin_cases i <;> simp [J]

lemma star_square (a : W) : star (star a) = a := by
  ext i
  fin_cases i <;> simp [star]

lemma star_add (a b : W) : star (a + b) = star a + star b := by
  ext i
  fin_cases i <;> simp [star, add_comm]

lemma star_smul (c : ℝ) (a : W) : star (c • a) = c • star a := by
  ext i
  fin_cases i <;> simp [star]

lemma star_self_adjoint (a b : W) : ⟪star a, b⟫ = ⟪a, star b⟫ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, star]
  ring

lemma star_isometry (a b : W) : ⟪star a, star b⟫ = ⟪a, b⟫ := by
  rw [star_self_adjoint, star_square]

lemma J_inner (u v : V) : ⟪J u, J v⟫ = ⟪u, v⟫ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, J]
  ring

lemma inner_self_J (v : V) : ⟪v, J v⟫ = 0 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, J]
  ring

lemma wedge_inner (u v a b : V) :
    ⟪wedge u v, wedge a b⟫ = ⟪u, a⟫ * ⟪v, b⟫ - ⟪u, b⟫ * ⟪v, a⟫ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, wedge]
  ring

lemma star_fundamental : star fundamental = fundamental := by
  ext i
  fin_cases i <;> simp [star, fundamental]

lemma fundamental_norm_sq : ‖fundamental‖ ^ 2 = 2 := by
  norm_num [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, fundamental]

lemma line_selfDualPart (v : V) : selfDualPart (line v) =
    (‖v‖ ^ 2 / 2) • fundamental := by
  rw [EuclideanSpace.real_norm_sq_eq]
  ext i
  fin_cases i <;>
    simp [selfDualPart, line, wedge, J, star, fundamental,
      Fin.sum_univ_succ] <;> ring

lemma line_norm_sq (v : V) : ‖line v‖ ^ 2 = (‖v‖ ^ 2) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, line, wedge_inner, J_inner, inner_self_J,
    zero_mul, sub_zero, real_inner_self_eq_norm_sq]
  ring

lemma fundamental_eval_line (v : V) : ⟪fundamental, line v⟫ = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [line, wedge, J, fundamental,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  ring

lemma unit_line_norm {v : V} (hv : ‖v‖ = 1) : ‖line v‖ = 1 := by
  have hs := line_norm_sq v
  rw [hv] at hs
  nlinarith [norm_nonneg (line v)]

lemma unit_line_selfDualPart {v : V} (hv : ‖v‖ = 1) :
    selfDualPart (line v) = (1 / 2 : ℝ) • fundamental := by
  rw [line_selfDualPart, hv]
  norm_num

theorem angular_identity (a b F G : W)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hF : ‖F‖ ^ 2 = 2) (hG : ‖G‖ ^ 2 = 2)
    (haF : selfDualPart a = (1 / 2 : ℝ) • F)
    (hbG : selfDualPart b = (1 / 2 : ℝ) • G) :
    ⟪a, star b⟫ = (1 / 2 : ℝ) * ‖a - b‖ ^ 2 -
      (1 / 4 : ℝ) * ‖F - G‖ ^ 2 := by
  have hp : ⟪F, G⟫ = 2 * (⟪a, b⟫ + ⟪a, star b⟫) := by
    have h := congrArg₂ (fun x y : W => ⟪x, y⟫) haF hbG
    dsimp [selfDualPart] at h
    simp only [real_inner_smul_left, real_inner_smul_right,
      inner_add_left, inner_add_right, star_self_adjoint, star_square] at h
    linarith
  rw [norm_sub_sq_real, norm_sub_sq_real, ha, hb, hF, hG]
  linarith

def jAction (a : W) : W := WithLp.toLp 2 ![a 0, a 4, -a 3, -a 2, a 1, a 5]

def antiInvariantPart (a : W) : W := (1 / 2 : ℝ) • (a - jAction a)

lemma jAction_square (a : W) : jAction (jAction a) = a := by
  ext i
  fin_cases i <;> simp [jAction]

lemma star_antiInvariantPart (a : W) : star (antiInvariantPart a) = antiInvariantPart a := by
  ext i
  fin_cases i <;> simp [star, antiInvariantPart, jAction] <;> ring

lemma antiInvariantPart_fundamental : antiInvariantPart fundamental = 0 := by
  ext i
  fin_cases i <;> simp [antiInvariantPart, jAction, fundamental]

def interior (ξ : V) (a : W) : V := WithLp.toLp 2
  ![-ξ 1 * a 0 - ξ 2 * a 1 - ξ 3 * a 2,
    ξ 0 * a 0 - ξ 2 * a 3 - ξ 3 * a 4,
    ξ 0 * a 1 + ξ 1 * a 3 - ξ 3 * a 5,
    ξ 0 * a 2 + ξ 1 * a 4 + ξ 2 * a 5]

theorem closed_lift_principal_symbol (ξ : V) (a : W) :
    antiInvariantPart (wedge ξ (interior ξ (antiInvariantPart a))) =
      (‖ξ‖ ^ 2 / 2) • antiInvariantPart a := by
  rw [EuclideanSpace.real_norm_sq_eq]
  ext i
  fin_cases i <;>
    simp [antiInvariantPart, jAction, wedge, interior, Fin.sum_univ_succ] <;> ring

end TamingCompatibility.UnitaryFrame

end

end OAI
