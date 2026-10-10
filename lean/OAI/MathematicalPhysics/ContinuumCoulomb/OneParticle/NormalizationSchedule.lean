import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.NormalizationQuadrature
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarNormalizationBox

namespace OAI

/-! A fixed polynomial schedule for the actual normalization integral.
The outer square grows linearly with inverse accuracy; both nested mesh
counts and the inner resolvent accuracy are explicit natural polynomials. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.NormalizationSchedule

irreducible_def radius (P : ℕ) : ℕ := 8192 * (P + 1)
def meshPrefix (P : ℕ) : ℕ := 4096 * radius P ^ 3
def mesh (P : ℕ) : ℕ := meshPrefix P * (P + 1)
def accuracyPrefix (P : ℕ) : ℕ := 48 * radius P ^ 2
def accuracy (P : ℕ) : ℕ := accuracyPrefix P * (P + 1)

def input (P : ℕ) : NormalizationQuadrature.Input :=
  (mesh P, ((2 * radius P, accuracy P),
    (-(radius P : ℚ), (2 * (radius P : ℚ)) / (mesh P : ℚ))))

def approximate (P : ℕ) : ℚ := NormalizationQuadrature.value (input P)

theorem radius_positive (P : ℕ) : 0 < radius P := by rw [radius_def]; positivity

theorem mesh_positive (P : ℕ) : 0 < mesh P := by
  have h := radius_positive P
  unfold mesh meshPrefix
  positivity

theorem input_step_nonnegative (P : ℕ) : 0 ≤ ((input P).2.2.2 : ℝ) := by
  have hL : (0 : ℚ) < radius P := by exact_mod_cast radius_positive P
  have hN : (0 : ℚ) < mesh P := by exact_mod_cast mesh_positive P
  change 0 ≤ (((2 * (radius P : ℚ)) / (mesh P : ℚ) : ℚ) : ℝ)
  exact_mod_cast (div_nonneg (by positivity : (0 : ℚ) ≤ 2 * radius P) hN.le)

theorem input_endpoint (P : ℕ) :
    RationalQuadratureProgram.node (input P).2.2.1 (input P).2.2.2 (mesh P) = (radius P : ℚ) := by
  have hN : (mesh P : ℚ) ≠ 0 := by exact_mod_cast (mesh_positive P).ne'
  change -(radius P : ℚ) + (mesh P : ℚ) * (2 * (radius P : ℚ) / (mesh P : ℚ)) = _
  field_simp
  ring

theorem input_node_mem (P i : ℕ) (hi : i ≤ mesh P) :
    (RationalQuadratureProgram.node (input P).2.2.1 (input P).2.2.2 i : ℝ) ∈
      Set.Icc (-(radius P : ℝ)) (radius P : ℝ) := by
  have h := UniformQuadrature.node_mem (a := ((input P).2.2.1 : ℝ))
    (input_step_nonnegative P) hi
  rw [← RationalQuadratureProgram.node_cast, ← RationalQuadratureProgram.node_cast,
    input_endpoint P] at h
  simpa only [input, Rat.cast_neg, Rat.cast_natCast] using h

theorem input_nodes_norm (P i j : ℕ) (hi : i < mesh P) (hj : j < mesh P) :
    ‖PlanarForcingProgram.position
      (RationalQuadratureProgram.node (input P).2.2.1 (input P).2.2.2 i,
       RationalQuadratureProgram.node (input P).2.2.1 (input P).2.2.2 j)‖ ≤
      (2 * radius P : ℕ) := by
  rw [rationalPosition_eq_pair, Nat.cast_mul, Nat.cast_ofNat]
  exact planarPair_norm_box (by exact_mod_cast (radius_positive P).le)
    ⟨input_node_mem P i hi.le, input_node_mem P j hj.le⟩

theorem numerical_budget {L S N K : ℝ} (hL : 0 < L) (hS : 0 < S)
    (hN : N = 4096 * L ^ 3 * S) (hK : K = 48 * L ^ 2 * S)
    (hLS : L = 8192 * S) :
    (N * (2 * L / N)) ^ 2 * (128 * (2 * L / N) + 3 / (K + 1)) +
      1024 * Real.exp (-(1 / 2 : ℝ) * L) ≤ S⁻¹ := by
  have hN0 : 0 < N := by rw [hN]; positivity
  have hK0 : 0 < K := by rw [hK]; positivity
  have hlen : N * (2 * L / N) = 2 * L := by field_simp [hN0.ne']
  have hs : (2 * L) ^ 2 * (128 * (2 * L / N)) = (4 * S)⁻¹ := by
    rw [hN]
    field_simp [hL.ne', hS.ne']
    ring
  have hb : (2 * L) ^ 2 * (3 / (K + 1)) ≤ (4 * S)⁻¹ := by
    calc
      _ ≤ (2 * L) ^ 2 * (3 / K) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by norm_num) hK0 (by linarith)) (sq_nonneg _)
      _ = _ := by rw [hK]; field_simp [hL.ne', hS.ne']; ring
  have ht : 1024 * Real.exp (-(1 / 2 : ℝ) * L) ≤ (4 * S)⁻¹ := by
    calc
      _ ≤ 1024 * (L / 2)⁻¹ := by
        have he := ResolventSchedule.exp_tail_le_inverse (show 0 < L / 2 by positivity)
        have he' : Real.exp (-(1 / 2 : ℝ) * L) ≤ (L / 2)⁻¹ := by
          rw [show -(1 / 2 : ℝ) * L = -(L / 2) by ring]
          exact he
        exact mul_le_mul_of_nonneg_left he' (by norm_num)
      _ = _ := by rw [hLS]; field_simp [hS.ne']; ring
  rw [hlen, mul_add, hs]
  have hsmall : 3 * (4 * S)⁻¹ ≤ S⁻¹ := by
    rw [mul_inv]
    norm_num
    nlinarith [inv_pos.mpr hS]
  linarith

theorem approximation_error (P : ℕ) :
    |(approximate P : ℝ) - (∫ r, planarResolventMode r ^ 2)| ≤ ((P : ℝ) + 1)⁻¹ := by
  let L := (radius P : ℝ)
  let N := (mesh P : ℝ)
  let K := (accuracy P : ℝ)
  let S := (P : ℝ) + 1
  have hL : 0 < L := by
    dsimp only [L]
    exact_mod_cast radius_positive P
  have hS : 0 < S := by dsimp [S]; positivity
  have hN : N = 4096 * L ^ 3 * S := by
    dsimp [N, L, S, mesh, meshPrefix]
    push_cast
    rfl
  have hK : K = 48 * L ^ 2 * S := by
    dsimp [K, L, S, accuracy, accuracyPrefix]
    push_cast
    rfl
  have hLS : L = 8192 * S := by
    dsimp only [L, S]
    rw [radius_def]
    push_cast
    rfl
  have hquad := NormalizationQuadrature.error (input P) (input_step_nonnegative P)
    (fun i hi j hj => input_nodes_norm P i j hi hj)
  have hend : RationalQuadratureProgram.node (input P).2.2.1 (input P).2.2.2
      (input P).1 = (radius P : ℚ) := input_endpoint P
  rw [hend] at hquad
  have hquad' : |(approximate P : ℝ) - planarNormalizationBox L| ≤
      (N * (2 * L / N)) ^ 2 * (128 * (2 * L / N) + 3 / (K + 1)) := by
    dsimp only [L, N, K]
    simpa only [approximate, planarNormalizationBox, input, Rat.cast_neg, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, div_eq_mul_inv, Rat.cast_inv] using hquad
  have htail := planarNormalizationBox_error hL.le
  have htotal := (abs_sub_le (approximate P : ℝ) (planarNormalizationBox L)
    (∫ r, planarResolventMode r ^ 2)).trans (add_le_add hquad' htail)
  exact htotal.trans (numerical_budget hL hS hN hK hLS)

end ContinuumCoulomb.NormalizationSchedule

end

end OAI
