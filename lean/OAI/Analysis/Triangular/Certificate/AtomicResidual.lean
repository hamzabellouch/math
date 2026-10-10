import OAI.Analysis.Triangular.Certificate.AtomicMatrix
import OAI.Analysis.Triangular.Certificate.AtomicCandidate

namespace OAI

noncomputable section
open scoped BigOperators

namespace AtomicTriangular.FiniteCertificate.AtomicMatrix
open AtomicTriangular.Interval Matrix

/-- Interval multiplication with floor and ceiling at the common integer grid. -/
def exactMul (a b : RI) : RI :=
  ⟨imin4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi) / scale,
   -((-imax4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi)) / scale)⟩

lemma exactMul_mem {a b : RI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (exactMul a b).Mem (x*y) := by
  refine ⟨(RI.mem_mul hx hy).1, ?_⟩
  have hh := (four_bounds hx hy).2
  have hu := (div_floor_bounds
    (-imax4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi))
    scale scale_int_pos).1
  have hc := neg_le_neg hu
  simp only [Int.cast_neg, neg_neg] at hc
  apply (mul_le_mul_iff_right₀ scale_pos).mp
  dsimp only [exactMul]
  calc
    (scale : ℝ) * (scale * (x*y)) = (scale*x)*(scale*y) := by ring
    _ ≤ (imax4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi) : ℝ) := by
      simpa only [imax4, Int.cast_max, Int.cast_mul] using hh
    _ ≤ _ := hc
    _ = _ := by push_cast; ring

def exactMatrixMul (a b : Fin 20 → Fin 20 → RI) (i j : Fin 20) : RI :=
  RI.sum (fun k => exactMul (a i k) (b k j))

lemma exactMatrixMul_mem {a b : Fin 20 → Fin 20 → RI}
    {A B : Matrix (Fin 20) (Fin 20) ℝ}
    (ha : ∀ i j, (a i j).Mem (A i j)) (hb : ∀ i j, (b i j).Mem (B i j))
    (i j : Fin 20) : (exactMatrixMul a b i j).Mem ((A*B) i j) :=
  RI.mem_sum (fun k => exactMul_mem (ha i k) (hb k j))

/-- Side zero is the sum block I−R; side one is the difference block I+R. -/
def system (side : Fin 2) (i j : Fin 20) : RI :=
  if side.val = 0 then (matrixOne i j).sub (literalR i j)
  else (matrixOne i j).add (literalR i j)

def systemValue (side : Fin 2) : Matrix (Fin 20) (Fin 20) ℝ :=
  if side.val = 0 then 1 - RValue else 1 + RValue

lemma system_mem (side : Fin 2) (i j : Fin 20) :
    (system side i j).Mem (systemValue side i j) := by
  by_cases hs : side.val = 0
  · simpa only [system, systemValue, ite_eq_left hs, Matrix.sub_apply] using
      RI.mem_sub (matrixOne_mem i j) (literalR_mem i j)
  · simpa only [system, systemValue, ite_eq_right hs, Matrix.add_apply] using
      RI.mem_add (matrixOne_mem i j) (literalR_mem i j)

/-- The full right residual of the rational inverse candidate. -/
def residual (side : Fin 2) (i j : Fin 20) : RI :=
  (matrixOne i j).sub (exactMatrixMul (system side) (candidate side) i j)

lemma residual_mem (side : Fin 2) (i j : Fin 20) :
    (residual side i j).Mem ((1 - systemValue side * candidateValue side) i j) :=
  RI.mem_sub (matrixOne_mem i j)
    (exactMatrixMul_mem (system_mem side) (candidate_mem side) i j)

def residualCorrection (side : Fin 2) (i j : Fin 20) : RI :=
  (candidate side i j).add (exactMatrixMul (candidate side) (residual side) i j)

lemma residualCorrection_mem (side : Fin 2) (i j : Fin 20) :
    (residualCorrection side i j).Mem
      ((candidateValue side + candidateValue side *
        (1 - systemValue side * candidateValue side)) i j) :=
  RI.mem_add (candidate_mem side i j)
    (exactMatrixMul_mem (candidate_mem side) (residual_mem side) i j)

/-- Second-order inverse enclosure, padded by the exact radius 2·10⁻¹⁷. -/
def inverseEnclosure (side : Fin 2) (i j : Fin 20) : RI :=
  (residualCorrection side i j).widen (2 * 10^43)

end AtomicTriangular.FiniteCertificate.AtomicMatrix

end

end OAI
