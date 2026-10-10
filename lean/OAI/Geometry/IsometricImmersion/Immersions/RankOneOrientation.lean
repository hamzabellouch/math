import OAI.Geometry.IsometricImmersion.Coordinates.OrientationNet
import OAI.Geometry.IsometricImmersion.Immersions.RankOne2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open scoped Matrix BigOperators
open WithLp

namespace SmoothLocal.Geometry

theorem exists_nonzero_dyad_of_symmetric_rank_one
    (H : Matrix (Fin 2) (Fin 2) ℝ) (hsym : Hᵀ = H) (hrank : H.rank = 1) :
    ∃ lam : ℝ, ∃ u : PlanarAxis, lam ≠ 0 ∧ u ≠ 0 ∧
      H = lam • Matrix.vecMulVec (ofLp u) (ofLp u) := by
  classical
  have hprops := (two_by_two_rank_eq_one_iff H).mp hrank
  have h10 : H 1 0 = H 0 1 := congrFun (congrFun hsym 0) 1
  have hd : H 0 0 * H 1 1 - H 0 1 ^ 2 = 0 := by
    simpa only [Matrix.det_fin_two, h10, pow_two] using hprops.2
  by_cases h00 : H 0 0 = 0
  · have h01 : H 0 1 = 0 := by rw [h00] at hd; nlinarith [sq_nonneg (H 0 1)]
    have h11 : H 1 1 ≠ 0 := by
      intro hz
      apply hprops.1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, hz]
    let u : PlanarAxis := toLp 2 ![0, H 1 1]
    have hu : u ≠ 0 := by
      intro hu0
      have hc := congrArg (fun w : PlanarAxis => w 1) hu0
      exact h11 (by simpa [u] using hc)
    refine ⟨(H 1 1)⁻¹, u, inv_ne_zero h11, hu, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u, Matrix.smul_apply, h00, h01, h10, h11]
  · let u : PlanarAxis := toLp 2 ![H 0 0, H 0 1]
    have hu : u ≠ 0 := by
      intro hu0
      have hc := congrArg (fun w : PlanarAxis => w 0) hu0
      exact h00 (by simpa [u] using hc)
    refine ⟨(H 0 0)⁻¹, u, inv_ne_zero h00, hu, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u, Matrix.smul_apply, h10] <;>
      field_simp [h00]
    nlinarith [hd]

theorem exists_unit_dyad_of_symmetric_rank_one
    (H : Matrix (Fin 2) (Fin 2) ℝ) (hsym : Hᵀ = H) (hrank : H.rank = 1) :
    ∃ lam : ℝ, ∃ v : PlanarAxis, lam ≠ 0 ∧ ‖v‖ = 1 ∧
      H = lam • Matrix.vecMulVec (ofLp v) (ofLp v) := by
  obtain ⟨μ, u, hμ, hu, hH⟩ := exists_nonzero_dyad_of_symmetric_rank_one H hsym hrank
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  refine ⟨μ * ‖u‖ ^ 2, ‖u‖⁻¹ • u, mul_ne_zero hμ (pow_ne_zero 2 hn),
    norm_smul_inv_norm (𝕜 := ℝ) hu, ?_⟩
  rw [hH]
  ext i j
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul]
  field_simp [hn]

def clockwiseAxis (a : PlanarAxis) : PlanarAxis := toLp 2 ![a 1, -a 0]

theorem planar_inner_coordinates (v a : PlanarAxis) :
    inner ℝ v a = v 0 * a 0 + v 1 * a 1 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct, Fin.sum_univ_two]
  ring

theorem clockwiseAxis_orthogonal (a : PlanarAxis) : inner ℝ a (clockwiseAxis a) = 0 := by
  rw [planar_inner_coordinates]
  change a 0 * a 1 + a 1 * (-a 0) = 0
  ring

theorem clockwiseAxis_unit {a : PlanarAxis} (ha : ‖a‖ = 1) : ‖clockwiseAxis a‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  change a 1 ^ 2 + (-a 0) ^ 2 = (1 : ℝ) ^ 2
  have hs := planarAxis_sq_sum ha
  nlinarith [hs]

theorem nearby_axis_inner_bounds {v a : PlanarAxis} (ha : ‖a‖ = 1)
    (hclose : dist v a < (1 / 1000 : ℝ)) :
    |inner ℝ v a - 1| < (1 / 1000 : ℝ) ∧
      |inner ℝ v (clockwiseAxis a)| < (1 / 1000 : ℝ) := by
  constructor
  · have hb := abs_real_inner_le_norm (v - a) a
    have heq : inner ℝ (v - a) a = inner ℝ v a - 1 := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, ha, one_pow]
    rw [heq, ha, mul_one, ← dist_eq_norm] at hb
    exact hb.trans_lt hclose
  · have hb := abs_real_inner_le_norm (v - a) (clockwiseAxis a)
    rw [inner_sub_left, clockwiseAxis_orthogonal, sub_zero,
      clockwiseAxis_unit ha, mul_one, ← dist_eq_norm] at hb
    exact hb.trans_lt hclose

def rotatedForm (H : Matrix (Fin 2) (Fin 2) ℝ) (a : PlanarAxis) :
    Matrix (Fin 2) (Fin 2) ℝ := (axisRotation a)ᵀ * H * axisRotation a

theorem rotated_dyad_entries (lam : ℝ) (v a : PlanarAxis) :
    rotatedForm (lam • Matrix.vecMulVec (ofLp v) (ofLp v)) a 1 1 =
        lam * (inner ℝ v a) ^ 2 ∧
      rotatedForm (lam • Matrix.vecMulVec (ofLp v) (ofLp v)) a 0 1 =
        lam * inner ℝ v (clockwiseAxis a) * inner ℝ v a := by
  constructor <;>
    simp only [rotatedForm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul] <;>
    simp [axisRotation, clockwiseAxis, planar_inner_coordinates] <;> ring

theorem rotated_dyad_admissible_axis (lam : ℝ) (hlam : lam ≠ 0) (v a : PlanarAxis)
    (ha : ‖a‖ = 1) (hclose : dist v a < (1 / 1000 : ℝ)) :
    rotatedForm (lam • Matrix.vecMulVec (ofLp v) (ofLp v)) a 1 1 ≠ 0 ∧
      |rotatedForm (lam • Matrix.vecMulVec (ofLp v) (ofLp v)) a 0 1 /
        rotatedForm (lam • Matrix.vecMulVec (ofLp v) (ofLp v)) a 1 1| < (1 / 100 : ℝ) := by
  obtain ⟨hcos, hsin⟩ := nearby_axis_inner_bounds ha hclose
  have hcospos : 0 < inner ℝ v a := by
    have hl := (abs_lt.mp hcos).1
    linarith
  obtain ⟨hyy, hxy⟩ := rotated_dyad_entries lam v a
  constructor
  · rw [hyy]
    exact mul_ne_zero hlam (pow_ne_zero 2 hcospos.ne')
  · rw [hxy, hyy]
    have hquot : lam * inner ℝ v (clockwiseAxis a) * inner ℝ v a /
        (lam * (inner ℝ v a) ^ 2) = inner ℝ v (clockwiseAxis a) / inner ℝ v a := by
      field_simp [hlam, hcospos.ne']
    rw [hquot, abs_div, abs_of_pos hcospos]
    apply (div_lt_iff₀ hcospos).mpr
    have hl := (abs_lt.mp hcos).1
    nlinarith

theorem exists_orientationRotation_for_rank_one
    (H : Matrix (Fin 2) (Fin 2) ℝ) (hsym : Hᵀ = H) (hrank : H.rank = 1) :
    ∃ R ∈ orientationRotations,
      (Rᵀ * H * R) 1 1 ≠ 0 ∧
      |(Rᵀ * H * R) 0 1 / (Rᵀ * H * R) 1 1| < (1 / 100 : ℝ) := by
  classical
  obtain ⟨lam, v, hlam, hv, hH⟩ := exists_unit_dyad_of_symmetric_rank_one H hsym hrank
  obtain ⟨a, ha, hclose⟩ := orientationAxes_cover v hv
  refine ⟨axisRotation a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
  rw [hH]
  exact rotated_dyad_admissible_axis lam hlam v a (orientationAxes_unit a ha) hclose

end SmoothLocal.Geometry

end

end OAI
