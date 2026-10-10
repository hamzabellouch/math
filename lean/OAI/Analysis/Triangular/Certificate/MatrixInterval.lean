import OAI.Analysis.Triangular.Certificate.WaveIntervals
import OAI.Analysis.Triangular.Auxiliary.MatrixNorm

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Interval
open Matrix AtomicTriangular.MatrixBounds

def RI.singleton (z : ℤ) : RI := ⟨z,z⟩
lemma RI.mem_singleton (z : ℤ) : (RI.singleton z).Mem ((z:ℝ)/(scale:ℝ)) := by
  have hs : (scale:ℝ) ≠ 0 := scale_pos.ne'
  have hh : (scale:ℝ)*((z:ℝ)/(scale:ℝ)) = (z:ℝ) := by field_simp
  constructor <;> dsimp only [RI.Mem,RI.singleton] <;> rw [hh]
lemma RI.le_upper {a : RI} {x : ℝ} (hx : a.Mem x) : x ≤ (a.hi:ℝ)/(scale:ℝ) := by
  apply (le_div_iff₀ scale_pos).mpr
  simpa only [mul_comm] using hx.2
lemma RI.lower_le {a : RI} {x : ℝ} (hx : a.Mem x) : (a.lo:ℝ)/(scale:ℝ) ≤ x := by
  apply (div_le_iff₀ scale_pos).mpr
  simpa only [mul_comm] using hx.1

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
def matrixMul (a : m → n → RI) (b : n → p → RI) (i : m) (j : p) : RI :=
  RI.sum (fun k => (a i k).mul (b k j))
omit [Fintype m] [Fintype p] in
lemma matrixMul_mem {a : m → n → RI} {b : n → p → RI}
    {A : Matrix m n ℝ} {B : Matrix n p ℝ} (ha : ∀ i j, (a i j).Mem (A i j))
    (hb : ∀ i j, (b i j).Mem (B i j)) (i : m) (j : p) :
    (matrixMul a b i j).Mem ((A*B) i j) :=
  RI.mem_sum (fun k => RI.mem_mul (ha i k) (hb k j))
def matrixOne [DecidableEq n] (i j : n) : RI := RI.point (if i=j then 1 else 0)
omit [Fintype n] in
lemma matrixOne_mem [DecidableEq n] (i j : n) : (matrixOne i j).Mem ((1:Matrix n n ℝ) i j) := by
  simpa only [matrixOne,Matrix.one_apply,Int.cast_ite,Int.cast_zero,Int.cast_one] using
    RI.mem_point (if i=j then 1 else 0)

def matrixColBound (a : m → n → RI) (j : n) : ℤ := ∑ i, ((a i j).abs).hi
lemma matrixNorm_bound [Nonempty n] {a : m → n → RI} {A : Matrix m n ℝ} {b : ℤ}
    (ha : ∀ i j, (a i j).Mem (A i j)) (hb : ∀ j, matrixColBound a j ≤ b) :
    matNorm A ≤ (b:ℝ)/(scale:ℝ) := by
  apply matNorm_le
  intro j
  have hh := (RI.mem_sum (fun i => RI.mem_abs (ha i j))).2
  apply (le_div_iff₀ scale_pos).mpr
  change colNorm A j * (scale:ℝ) ≤ (b:ℝ)
  rw [mul_comm]
  apply hh.trans
  exact_mod_cast hb j

lemma matrixEntry_le_norm [Nonempty n] (A : Matrix m n ℝ) (i : m) (j : n) :
    |A i j| ≤ matNorm A := by
  have hh : |A i j| ≤ colNorm A j :=
    Finset.single_le_sum (fun k _ => abs_nonneg (A k j)) (Finset.mem_univ i)
  exact hh.trans (colNorm_le_matNorm A j)
end AtomicTriangular.Interval
end

end OAI
