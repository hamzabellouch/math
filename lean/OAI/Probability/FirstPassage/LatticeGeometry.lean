import OAI.Probability.FirstPassage.SpatialModulus
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped Topology

noncomputable def latticeEmbed (z : Vertex) : Plane :=
  WithLp.toLp 2 ![(z.1 : ℝ), (z.2 : ℝ)]

@[simp] theorem latticeEmbed_zero : latticeEmbed 0 = 0 := by ext i; fin_cases i <;> simp [latticeEmbed]
@[simp] theorem latticeFloor_embed (z : Vertex) : latticeFloor (latticeEmbed z) = z := by
  simp [latticeFloor, latticeEmbed]

@[simp] theorem latticeEmbed_sub (z w : Vertex) :
    latticeEmbed (z-w) = latticeEmbed z - latticeEmbed w := by
  ext i
  fin_cases i <;> simp [latticeEmbed]

theorem plane_coordinate_le_norm (v : Plane) (i : Fin 2) : |v i| ≤ ‖v‖ :=
  PiLp.norm_apply_le v i

theorem plane_norm_le_coordinates (v : Plane) : ‖v‖ ≤ |v 0| + |v 1| := by
  let x : Plane := PiLp.single 2 0 (v 0)
  let y : Plane := PiLp.single 2 1 (v 1)
  have hv : v = x+y := by
    ext i
    fin_cases i <;> simp [x,y]
  have hx : ‖x‖ = |v 0| := by simp [x]
  have hy : ‖y‖ = |v 1| := by simp [y]
  calc
    ‖v‖ = ‖x+y‖ := congrArg norm hv
    _ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
    _ = _ := by rw [hx,hy]

theorem latticeDistance_le_norm (p q : Vertex) :
    (latticeDistance p q : ℝ) ≤ 2 * ‖latticeEmbed q - latticeEmbed p‖ := by
  have h0 := plane_coordinate_le_norm (latticeEmbed q - latticeEmbed p) 0
  have h1 := plane_coordinate_le_norm (latticeEmbed q - latticeEmbed p) 1
  have hc (a : ℤ) : (a.natAbs : ℝ) = |(a : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  simp only [latticeDistance, Nat.cast_add, hc, Int.cast_sub]
  simpa only [latticeEmbed, PiLp.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, two_mul] using add_le_add h0 h1

theorem latticeFloor_error (v : Plane) : ‖latticeEmbed (latticeFloor v) - v‖ ≤ 2 := by
  have hi (i : Fin 2) : |(latticeEmbed (latticeFloor v) - v) i| ≤ 1 := by
    have hle := Int.floor_le (v i)
    have hlt := Int.lt_floor_add_one (v i)
    have he : (latticeEmbed (latticeFloor v) - v) i = (⌊v i⌋ : ℝ) - v i := by
      fin_cases i <;> rfl
    rw [he, abs_of_nonpos (by linarith)]
    linarith
  exact (plane_norm_le_coordinates _).trans (by linarith [hi 0, hi 1])

theorem latticeFloor_mem_box {v : Plane} {n : ℕ} (hv : ‖v‖ ≤ 2) (hn : 1 ≤ n) :
    latticeFloor ((n : ℝ) • v) ∈ latticeBox (3*n) := by
  have hi (i : Fin 2) : -(3*(n : ℤ)) ≤ ⌊(n : ℝ)*v i⌋ ∧
      ⌊(n : ℝ)*v i⌋ ≤ 3*(n : ℤ) := by
    have ha := (plane_coordinate_le_norm v i).trans hv
    have hb := abs_le.mp ha
    have hl := Int.floor_le ((n : ℝ)*v i)
    have hu := Int.lt_floor_add_one ((n : ℝ)*v i)
    constructor
    · have : -(3*(n : ℝ)) ≤ (⌊(n : ℝ)*v i⌋ : ℝ) := by
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      exact_mod_cast this
    · have : (⌊(n : ℝ)*v i⌋ : ℝ) ≤ 3*(n : ℝ) := by nlinarith
      exact_mod_cast this
  simpa only [latticeBox, Finset.mem_product, Finset.mem_Icc, latticeFloor,
    PiLp.smul_apply, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using And.intro (hi 0) (hi 1)

theorem latticeDistance_floor_le (v w : Plane) (n : ℕ) :
    (latticeDistance (latticeFloor ((n : ℝ) • v))
      (latticeFloor ((n : ℝ) • w)) : ℝ) ≤ 2 * (n : ℝ) * ‖w-v‖ + 8 := by
  have hd := latticeDistance_le_norm (latticeFloor ((n : ℝ) • v))
    (latticeFloor ((n : ℝ) • w))
  have he : latticeEmbed (latticeFloor ((n : ℝ) • w)) -
      latticeEmbed (latticeFloor ((n : ℝ) • v)) =
      (latticeEmbed (latticeFloor ((n : ℝ) • w)) - (n : ℝ) • w) +
      (n : ℝ) • (w-v) -
      (latticeEmbed (latticeFloor ((n : ℝ) • v)) - (n : ℝ) • v) := by
    rw [smul_sub]; abel
  have hb : ‖latticeEmbed (latticeFloor ((n : ℝ) • w)) -
      latticeEmbed (latticeFloor ((n : ℝ) • v))‖ ≤
      ‖latticeEmbed (latticeFloor ((n : ℝ) • w)) - (n : ℝ) • w‖ +
      ‖(n : ℝ) • (w-v)‖ +
      ‖latticeEmbed (latticeFloor ((n : ℝ) • v)) - (n : ℝ) • v‖ := by
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  rw [norm_smul, Real.norm_natCast] at hb
  nlinarith [latticeFloor_error ((n : ℝ) • v), latticeFloor_error ((n : ℝ) • w)]

theorem timeConstantNorm_lipschitz_bound (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v w, |μ v - μ w| ≤ B * ‖v-w‖ := by
  let e0 : Plane := PiLp.single 2 0 1
  let e1 : Plane := PiLp.single 2 1 1
  let B := μ e0 + μ e1 + 1
  have hB : 0 < B := by dsimp [B]; linarith [hμ.nonneg e0, hμ.nonneg e1]
  have hu (v : Plane) : μ v ≤ B * ‖v‖ := by
    have he : v = v 0 • e0 + v 1 • e1 := by
      ext i; fin_cases i <;> simp [e0, e1]
    have ht := hμ.triangle (v 0 • e0) (v 1 • e1)
    rw [← he, hμ.homogeneous, hμ.homogeneous] at ht
    have h0 := mul_le_mul_of_nonneg_right (plane_coordinate_le_norm v 0) (hμ.nonneg e0)
    have h1 := mul_le_mul_of_nonneg_right (plane_coordinate_le_norm v 1) (hμ.nonneg e1)
    dsimp [B]
    nlinarith [norm_nonneg v]
  refine ⟨B, hB, ?_⟩
  intro v w
  apply abs_le.mpr
  have h1 := hμ.triangle (v-w) w
  have h2 := hμ.triangle (w-v) v
  simp only [sub_add_cancel] at h1 h2
  have hu1 := hu (v-w)
  have hu2 := hu (w-v)
  rw [norm_sub_rev] at hu2
  constructor <;> linarith

end PlanarFPP

end OAI
