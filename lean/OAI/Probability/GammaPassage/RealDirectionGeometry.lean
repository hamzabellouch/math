import OAI.Probability.FirstPassage.Target
import OAI.Probability.FirstPassage.Reversal
import OAI.Probability.FirstPassage.SpatialModulus
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.Int

namespace OAI

namespace GammaFPP.RealDirectionBridge
open PlanarFPP MeasureTheory Filter Set
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

theorem passageTime_origin_difference_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) : |passageTime w 0 p-passageTime w 0 q| ≤ passageTime w p q := by
  have h1 := passageTime_triangle w hw 0 q p
  have h2 := passageTime_triangle w hw 0 p q
  rw [passageTime_symm w hw q p] at h1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma lattice_mem_box_of_norm (p : Vertex) (n : ℕ) (hp : ‖latticeEmbed p‖ ≤ n) :
    p ∈ latticeBox n := by
  have hi (i : Fin 2) := (plane_coordinate_le_norm (latticeEmbed p) i).trans hp
  have h₁ : |p.1| ≤ (n : ℤ) := by exact_mod_cast (show |(p.1 : ℝ)| ≤ n from hi 0)
  have h₂ : |p.2| ≤ (n : ℤ) := by exact_mod_cast (show |(p.2 : ℝ)| ≤ n from hi 1)
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp h₁),Finset.mem_Icc.mpr (abs_le.mp h₂)⟩

lemma floor_real_ratio_tendsto (M : ℝ) (hM : 0 < M) :
    Tendsto (fun t : ℝ => (⌊t/M⌋₊ : ℝ)/t) atTop (𝓝 (1/M)) := by
  simpa [div_eq_mul_inv,mul_comm] using
    (tendsto_nat_floor_mul_div_atTop (inv_nonneg.mpr hM.le))

noncomputable def scaledLatticePoint (t : ℝ) (p : Vertex) : Plane :=
  (1/t) • latticeEmbed p

lemma scaledLatticePoint_norm (t : ℝ) (ht : 0 < t) (p : Vertex) :
    ‖scaledLatticePoint t p‖ = ‖latticeEmbed p‖/t := by
  rw [scaledLatticePoint,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr ht)]
  ring

lemma scaledLatticePoint_sub_norm (t : ℝ) (ht : 0 < t) (p q : Vertex) :
    ‖scaledLatticePoint t p-scaledLatticePoint t q‖ = ‖latticeEmbed p-latticeEmbed q‖/t := by
  rw [scaledLatticePoint,scaledLatticePoint,← smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr ht)]
  ring

lemma scaled_floor_error (t : ℝ) (ht : 0 < t) (v : Plane) :
    ‖scaledLatticePoint t (latticeFloor (t • v))-v‖ ≤ 2/t := by
  have he : scaledLatticePoint t (latticeFloor (t • v))-v =
      (1/t) • (latticeEmbed (latticeFloor (t • v))-t • v) := by
    rw [smul_sub,smul_smul,one_div_mul_cancel ht.ne',one_smul]
    rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr ht)]
  simpa only [one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using
    mul_le_mul_of_nonneg_left (latticeFloor_error (t • v)) (le_of_lt (one_div_pos.mpr ht))

lemma scaled_floor_tendsto (v : Plane) :
    Tendsto (fun t : ℝ => scaledLatticePoint t (latticeFloor (t • v))) atTop (𝓝 v) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_gt_atTop (max 0 (2/ε))] with t ht
  have ht0 : 0 < t := (le_max_left _ _).trans_lt ht
  rw [dist_eq_norm]
  exact (scaled_floor_error t ht0 v).trans_lt ((div_lt_iff₀ ht0).mpr
    (by have hh := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt ht); nlinarith))

lemma latticeEmbed_nsmul (n : ℕ) (z : Vertex) :
    latticeEmbed (n • z) = (n : ℝ) • latticeEmbed z := by
  ext i
  fin_cases i <;> simp [latticeEmbed,nsmul_eq_mul]

lemma scaled_lattice_ray_tendsto (z : Vertex) (M : ℝ) (hM : 0 < M) :
    Tendsto (fun t : ℝ => scaledLatticePoint t (⌊t/M⌋₊ • z)) atTop
      (𝓝 ((1/M) • latticeEmbed z)) := by
  have h := (floor_real_ratio_tendsto M hM).smul_const (latticeEmbed z)
  simpa only [scaledLatticePoint,latticeEmbed_nsmul,smul_smul,one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using h

lemma passageTime_real_lattice_ray_tendsto (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ)
    (hray : ∀ z : Vertex, Tendsto (fun n : ℕ => passageTime w 0 (n • z)/n)
      atTop (𝓝 (μ (latticeEmbed z)))) (z : Vertex) (M : ℝ) (hM : 0 < M) :
    Tendsto (fun t : ℝ => passageTime w 0 (⌊t/M⌋₊ • z)/t) atTop
      (𝓝 (μ ((1/M) • latticeEmbed z))) := by
  have hn : Tendsto (fun t : ℝ => ⌊t/M⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const hM)
  have hh := ((hray z).comp hn).mul (floor_real_ratio_tendsto M hM)
  have he : (fun t : ℝ => passageTime w 0 (⌊t/M⌋₊ • z)/t) =ᶠ[atTop]
      (fun t : ℝ => (passageTime w 0 (⌊t/M⌋₊ • z)/(⌊t/M⌋₊ : ℝ))*((⌊t/M⌋₊ : ℝ)/t)) := by
    filter_upwards [hn.eventually (eventually_ge_atTop 1)] with t ht
    have hn0 : (⌊t/M⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (show ⌊t/M⌋₊ ≠ 0 by omega)
    field_simp
  rw [hμ.homogeneous,abs_of_pos (one_div_pos.mpr hM),mul_comm]
  exact hh.congr' he.symm

end GammaFPP.RealDirectionBridge

end OAI
