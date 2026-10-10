import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Max

namespace OAI

/-!+# Maximizing bases and normalized box coefficients

This is the basis-exchange step in the manuscript's box calculus. A nonzero
coefficient permits column replacement. Maximality of the basis weight then
makes the exponential rescaling factor at most one.
-/

noncomputable section

open scoped BigOperators

namespace PolycyclicRecognition

variable {I : Type*} {n : ℕ}

/-- The columns chosen from a finite list of vectors. -/
def columnBasisMatrix (v : I → Fin n → ℝ) (b : Fin n → I) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => v (b j) i

def columnBasisWeight (w : I → ℝ) (b : Fin n → I) : ℝ := ∑ j, w (b j)

/-- A genuine invertible column basis maximizing the prescribed total weight. -/
def IsMaximizingColumnBasis (v : I → Fin n → ℝ) (w : I → ℝ) (b : Fin n → I) : Prop :=
  (columnBasisMatrix v b).det ≠ 0 ∧
    ∀ d : Fin n → I, (columnBasisMatrix v d).det ≠ 0 →
      columnBasisWeight w d ≤ columnBasisWeight w b

theorem exists_maximizingColumnBasis [Fintype I]
    (v : I → Fin n → ℝ) (w : I → ℝ)
    (hb : ∃ b : Fin n → I, (columnBasisMatrix v b).det ≠ 0) :
    ∃ b, IsMaximizingColumnBasis v w b := by
  classical
  let S := Finset.univ.filter fun b : Fin n → I => (columnBasisMatrix v b).det ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨b, hb⟩ := hb
    exact ⟨b, by simpa [S] using hb⟩
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image S (columnBasisWeight w) hS
  refine ⟨b, (Finset.mem_filter.mp hb).2, ?_⟩
  intro d hd
  exact hmax d (by simpa [S] using hd)

/-- A vector with nonzero coordinate at column `j` can replace that column.
The determinant identity is the exact algebraic exchange witness. -/
theorem det_columnBasis_update
    (v : I → Fin n → ℝ) (b : Fin n → I) (y : I) (j : Fin n)
    (c : Fin n → ℝ) (hc : ∀ k, v y k = ∑ i, c i * v (b i) k) :
    (columnBasisMatrix v (Function.update b j y)).det =
      c j * (columnBasisMatrix v b).det := by
  have hm : columnBasisMatrix v (Function.update b j y) =
      (columnBasisMatrix v b).updateCol j (v y) := by
    ext k i
    by_cases hi : i = j <;> simp [columnBasisMatrix, Matrix.updateCol, hi]
  rw [hm]
  have hv : v y = fun k => ∑ i, c i • columnBasisMatrix v b k i := by
    funext k
    simpa only [smul_eq_mul, columnBasisMatrix] using hc k
  rw [hv, Matrix.det_updateCol_sum, smul_eq_mul]

/-- Maximal total weight gives domination whenever the coordinate is nonzero. -/
theorem weight_le_of_nonzero_coordinate
    (v : I → Fin n → ℝ) (w : I → ℝ) (b : Fin n → I)
    (hb : IsMaximizingColumnBasis v w b) (y : I) (j : Fin n)
    (c : Fin n → ℝ) (hc : ∀ k, v y k = ∑ i, c i * v (b i) k)
    (hcj : c j ≠ 0) : w y ≤ w (b j) := by
  have hd : (columnBasisMatrix v (Function.update b j y)).det ≠ 0 := by
    rw [det_columnBasis_update v b y j c hc]
    exact mul_ne_zero hcj hb.1
  have h := hb.2 (Function.update b j y) hd
  have hw : (fun i => w (Function.update b j y i)) =
      Function.update (fun i => w (b i)) j (w y) := by
    funext i
    by_cases hi : i = j <;> simp [hi]
  unfold columnBasisWeight at h
  rw [hw, Finset.sum_update_of_mem (Finset.mem_univ j)] at h
  simp only [Finset.sdiff_singleton_eq_erase] at h
  have hs := Finset.sum_erase_add Finset.univ (fun i => w (b i)) (Finset.mem_univ j)
  linarith

/-- Scaling a maximizing basis introduces no growth in its coordinate
coefficients. Zero coordinates require no weight comparison. -/
theorem normalized_coordinate_le
    (v : I → Fin n → ℝ) (w : I → ℝ) (b : Fin n → I)
    (hb : IsMaximizingColumnBasis v w b) (y : I) (j : Fin n)
    (c : Fin n → ℝ) (hc : ∀ k, v y k = ∑ i, c i * v (b i) k)
    {r : ℝ} (hr : 0 ≤ r) :
    |c j * Real.exp (r * (w y - w (b j)))| ≤ |c j| := by
  by_cases hz : c j = 0
  · simp [hz]
  have hw := weight_le_of_nonzero_coordinate v w b hb y j c hc hz
  have he : Real.exp (r * (w y - w (b j))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr hw))
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (abs_nonneg (c j))

/-- Coordinates in an invertible selected column basis. The definition also
exists for singular selections, which simplifies the finite uniform bound. -/
def columnCoordinates (v : I → Fin n → ℝ) (b : Fin n → I) (y : I) : Fin n → ℝ :=
  (columnBasisMatrix v b)⁻¹.mulVec (v y)

theorem columnCoordinates_repr (v : I → Fin n → ℝ) (b : Fin n → I)
    (hb : (columnBasisMatrix v b).det ≠ 0) (y : I) (k : Fin n) :
    v y k = ∑ i, columnCoordinates v b y i * v (b i) k := by
  have h : (columnBasisMatrix v b).mulVec (columnCoordinates v b y) = v y := by
    unfold columnCoordinates
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hb),
      Matrix.one_mulVec]
  simpa only [Matrix.mulVec, dotProduct, columnBasisMatrix, mul_comm] using
    (congrFun h k).symm

/-- A single constant controls every normalized coefficient, uniformly over
all weights, all maximizing bases, and all nonnegative scales. -/
theorem exists_uniform_normalized_coordinate_bound [Fintype I]
    (v : I → Fin n → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : I → ℝ) (b : Fin n → I),
      IsMaximizingColumnBasis v w b → ∀ (y : I) (j : Fin n) (r : ℝ), 0 ≤ r →
        |columnCoordinates v b y j * Real.exp (r * (w y - w (b j)))| ≤ C := by
  classical
  let C : ℝ := ∑ b : Fin n → I, ∑ y : I, ∑ j : Fin n, |columnCoordinates v b y j|
  refine ⟨C, ?_, ?_⟩
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _
  · intro w b hb y j r hr
    apply (normalized_coordinate_le v w b hb y j (columnCoordinates v b y)
      (columnCoordinates_repr v b hb.1 y) hr).trans
    calc
      |columnCoordinates v b y j| ≤ ∑ k : Fin n, |columnCoordinates v b y k| :=
        Finset.single_le_sum (f := fun k : Fin n => |columnCoordinates v b y k|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ z : I, ∑ k : Fin n, |columnCoordinates v b z k| :=
        Finset.single_le_sum (f := fun z : I => ∑ k : Fin n, |columnCoordinates v b z k|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ y)
      _ ≤ C := Finset.single_le_sum
        (f := fun d : Fin n → I => ∑ z : I, ∑ k : Fin n, |columnCoordinates v d z k|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ b)

/-- The bounded coefficients above reconstruct the scaled vector in the
scaled selected basis, exactly as in the weighted box definition. -/
theorem scaled_columnCoordinates_repr (v : I → Fin n → ℝ) (w : I → ℝ)
    (b : Fin n → I) (hb : (columnBasisMatrix v b).det ≠ 0)
    (y : I) (r : ℝ) (k : Fin n) :
    Real.exp (r * w y) * v y k =
      ∑ i, (columnCoordinates v b y i * Real.exp (r * (w y - w (b i)))) *
        (Real.exp (r * w (b i)) * v (b i) k) := by
  rw [columnCoordinates_repr v b hb y k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : Real.exp (r * (w y - w (b i))) * Real.exp (r * w (b i)) =
      Real.exp (r * w y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (r * w y) * (columnCoordinates v b y i * v (b i) k) =
        columnCoordinates v b y i * Real.exp (r * w y) * v (b i) k := by ring
    _ = columnCoordinates v b y i *
        (Real.exp (r * (w y - w (b i))) * Real.exp (r * w (b i))) * v (b i) k := by rw [he]
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
