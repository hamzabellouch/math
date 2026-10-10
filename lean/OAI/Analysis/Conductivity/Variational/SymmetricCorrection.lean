import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

section
open Matrix

def symmetricCorrection {m n : Type*} [Fintype m] [Fintype n]
    (E R : Matrix m n ℝ) (L : Matrix n m ℝ) : Matrix m m ℝ :=
  R * L + Lᵀ * Rᵀ - Lᵀ * (Eᵀ * R) * L

theorem symmetricCorrection_isSymm {m n : Type*} [Fintype m] [Fintype n]
    (E R : Matrix m n ℝ) (L : Matrix n m ℝ)
    (hER : (Eᵀ * R).IsSymm) : (symmetricCorrection E R L).IsSymm := by
  unfold Matrix.IsSymm symmetricCorrection
  simp only [transpose_sub, transpose_add, transpose_mul, transpose_transpose]
  have hsym : Rᵀ * E = Eᵀ * R := by simpa only [Matrix.IsSymm, transpose_mul, transpose_transpose] using hER
  rw [hsym]
  simp only [Matrix.mul_assoc, add_comm]

theorem symmetricCorrection_mul {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (E R : Matrix m n ℝ) (L : Matrix n m ℝ)
    (hL : L * E = 1) (hER : (Eᵀ * R).IsSymm) :
    symmetricCorrection E R L * E = R := by
  have hsym : Rᵀ * E = Eᵀ * R := by
    simpa only [Matrix.IsSymm, transpose_mul, transpose_transpose] using hER
  simp only [symmetricCorrection, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, hL,
    Matrix.mul_one, hsym]
  exact add_sub_cancel_right _ _

theorem gram_leftInverse {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (E : Matrix m n ℝ) (hE : LinearIndependent ℝ E.col) :
    ((Eᵀ * E)⁻¹ * Eᵀ) * E = 1 := by
  have hinj : Function.Injective E.mulVec := Matrix.mulVec_injective_iff.mpr hE
  have hker : LinearMap.ker (Eᵀ * E).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot.mpr hinj
  have hunit : IsUnit (Eᵀ * E).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp hker))
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit]

theorem symmetricCorrection_gram_spec {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (E R : Matrix m n ℝ) (hE : LinearIndependent ℝ E.col)
    (hER : (Eᵀ * R).IsSymm) :
    let H := symmetricCorrection E R ((Eᵀ * E)⁻¹ * Eᵀ)
    H.IsSymm ∧ H * E = R := by
  exact ⟨symmetricCorrection_isSymm E R _ hER,
    symmetricCorrection_mul E R _ (gram_leftInverse E hE) hER⟩

end

open Filter Topology Set TopologicalSpace

theorem dense_continuityPoints_of_closed_ball_preimages
    {X Y : Type*} [TopologicalSpace X] [BaireSpace X]
    [PseudoMetricSpace Y] [SeparableSpace Y] [Nonempty Y]
    (f : X → Y)
    (hclosed : ∀ y r, IsClosed (f ⁻¹' Metric.closedBall y r)) :
    Dense {x | ContinuousAt f x} := by
  let q : ℕ → Y := denseSeq Y
  have hq : DenseRange q := denseRange_denseSeq Y
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : ∀ n, 0 < r n := fun n => div_pos zero_lt_one (Nat.cast_add_one_pos n)
  let V : ℕ → Set X := fun n => ⋃ k, interior (f ⁻¹' Metric.closedBall (q k) (r n))
  have hVo : ∀ n, IsOpen (V n) := fun _ => isOpen_iUnion fun _ => isOpen_interior
  have hVd : ∀ n, Dense (V n) := by
    intro n
    apply dense_iUnion_interior_of_closed (fun k => hclosed (q k) (r n))
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨k, hk⟩ := hq.exists_dist_lt (f x) (hr n)
    exact Set.mem_iUnion.mpr ⟨k, hk.le⟩
  refine (dense_iInter_of_isOpen_nat hVo hVd).mono ?_
  intro x hx
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
  have hrε : 2 * r n < ε := by dsimp only [r]; linarith
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hx n)
  have hxf : dist (f x) (q k) ≤ r n :=
    interior_subset (s := f ⁻¹' Metric.closedBall (q k) (r n)) hk
  filter_upwards [isOpen_interior.mem_nhds hk] with y hy
  have hyf : dist (f y) (q k) ≤ r n :=
    interior_subset (s := f ⁻¹' Metric.closedBall (q k) (r n)) hy
  calc
    dist (f y) (f x) ≤ dist (f y) (q k) + dist (q k) (f x) := dist_triangle _ _ _
    _ ≤ r n + r n := add_le_add hyf (by rwa [dist_comm])
    _ < ε := by linarith

end ScalarConductivity

end

end OAI
