import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.HoppingQuadrature

namespace OAI

/-! An explicit polynomial mesh and inner precision for the actual compact
hopping numerator. The displacement is an input rational, not an oracle. -/

noncomputable section
namespace ContinuumCoulomb.HoppingSchedule

abbrev Input := (ℕ × ℕ) × ℚ

def mesh (P : ℕ) : ℕ := 4096 * (P + 1)
def accuracy (P : ℕ) : ℕ := 16 * (P + 1)

def argument (x : Input) : HoppingQuadrature.Input :=
  (mesh x.1.2, (((x.1.1 + 2, accuracy x.1.2), x.2),
    (-1, 2 / (mesh x.1.2 : ℚ))))

def approximate (x : Input) : ℚ := HoppingQuadrature.value (argument x)

theorem mesh_positive (P : ℕ) : 0 < mesh P := by unfold mesh; positivity

theorem argument_step_nonnegative (x : Input) : 0 ≤ ((argument x).2.2.2 : ℝ) := by
  change 0 ≤ ((2 / (mesh x.1.2 : ℚ) : ℚ) : ℝ)
  positivity

theorem argument_endpoint (x : Input) :
    RationalQuadratureProgram.node (argument x).2.2.1 (argument x).2.2.2
      (argument x).1 = 1 := by
  have hN : (mesh x.1.2 : ℚ) ≠ 0 := by exact_mod_cast (mesh_positive x.1.2).ne'
  change -(1 : ℚ) + (mesh x.1.2 : ℚ) * (2 / (mesh x.1.2 : ℚ)) = 1
  field_simp
  ring

theorem argument_node_mem (x : Input) (i : ℕ) (hi : i ≤ (argument x).1) :
    (RationalQuadratureProgram.node (argument x).2.2.1 (argument x).2.2.2 i : ℝ) ∈
      Set.Icc (-1 : ℝ) 1 := by
  have h := UniformQuadrature.node_mem (a := ((argument x).2.2.1 : ℝ))
    (argument_step_nonnegative x) hi
  rw [← RationalQuadratureProgram.node_cast, ← RationalQuadratureProgram.node_cast,
    argument_endpoint x] at h
  simpa only [argument, Rat.cast_neg, Rat.cast_one] using h

theorem argument_nodes_norm (x : Input) (hd : |(x.2 : ℝ)| ≤ (x.1.1 : ℝ))
    (i j : ℕ) (hi : i < (argument x).1) (hj : j < (argument x).1) :
    ‖PlanarForcingProgram.position
      (RationalQuadratureProgram.node (argument x).2.2.1 (argument x).2.2.2 i -
          (argument x).2.1.2,
       RationalQuadratureProgram.node (argument x).2.2.1 (argument x).2.2.2 j)‖ ≤
      ((argument x).2.1.1.1 : ℝ) := by
  have h := rationalShift_norm_bound x.2 _ _ hd
    (argument_node_mem x i hi.le) (argument_node_mem x j hj.le)
  simpa only [argument, Nat.cast_add, Nat.cast_ofNat] using h

theorem numerical_budget {S : ℝ} (hS : 0 < S) :
    4 * (128 * (2 / (4096 * S)) + (16 * S + 1)⁻¹) ≤ S⁻¹ := by
  have hm : 4 * (128 * (2 / (4096 * S))) = (4 * S)⁻¹ := by
    field_simp [hS.ne']
    ring
  have ha : 4 * (16 * S + 1)⁻¹ ≤ (4 * S)⁻¹ := by
    calc
      _ ≤ 4 * (16 * S)⁻¹ := mul_le_mul_of_nonneg_left
        (inv_anti₀ (by positivity) (by linarith)) (by norm_num)
      _ = _ := by field_simp [hS.ne']; ring
  rw [mul_add, hm]
  have he : 2 * (4 * S)⁻¹ ≤ S⁻¹ := by
    rw [mul_inv]
    norm_num
    nlinarith [inv_pos.mpr hS]
  linarith

theorem approximation_error (x : Input) (hd : |(x.2 : ℝ)| ≤ (x.1.1 : ℝ)) :
    |(approximate x : ℝ) - planarHoppingNumerator (x.2 : ℝ)| ≤ ((x.1.2 : ℝ) + 1)⁻¹ := by
  have hquad := HoppingQuadrature.error (argument x) (argument_step_nonnegative x)
    (fun i hi j hj => argument_nodes_norm x hd i j hi hj)
  rw [argument_endpoint x] at hquad
  have hlen : (mesh x.1.2 : ℝ) * (2 / (mesh x.1.2 : ℝ)) = 2 := by
    have hn : (mesh x.1.2 : ℝ) ≠ 0 := by exact_mod_cast (mesh_positive x.1.2).ne'
    field_simp
  have hquad' : |(approximate x : ℝ) - planarHoppingNumerator (x.2 : ℝ)| ≤
      4 * (128 * (2 / (mesh x.1.2 : ℝ)) + ((accuracy x.1.2 : ℝ) + 1)⁻¹) := by
    rw [planarHoppingNumerator_box]
    simpa only [approximate, argument, Rat.cast_neg, Rat.cast_one, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_natCast, hlen, show (2 : ℝ) ^ 2 = 4 by norm_num]
      using hquad
  apply hquad'.trans
  convert numerical_budget (S := (x.1.2 : ℝ) + 1) (by positivity) using 1
  simp only [mesh, accuracy, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]

end ContinuumCoulomb.HoppingSchedule

end

end OAI
