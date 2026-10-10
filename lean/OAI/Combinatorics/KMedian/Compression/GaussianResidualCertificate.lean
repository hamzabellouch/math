import Mathlib
import OAI.Combinatorics.KMedian.Compression.GaussianCircuit

namespace OAI


                                                   
section
namespace MetricKMedian.Gaussian
open Finset

def rowValue {R N : ℕ} (A : Fin R → Fin N → ℚ) (v : Fin R → ℚ) (j : Fin N) : ℚ :=
  ∑ i, A i j*v i

 theorem rowValue_sub {R N : ℕ} (A : Fin R → Fin N → ℚ) (u v : Fin R → ℚ)
    (t : ℚ) (j : Fin N) :
    rowValue A (fun i => u i-t*v i) j=rowValue A u j-t*rowValue A v j := by
  simp only [rowValue,mul_sub,sum_sub_distrib]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  ring

 theorem rowValue_smul {R N : ℕ} (A : Fin R → Fin N → ℚ) (v : Fin R → ℚ)
    (t : ℚ) (j : Fin N) : rowValue A (fun i => t*v i) j=t*rowValue A v j := by
  simp only [rowValue,mul_sum]
  apply sum_congr rfl
  intro i _
  ring

structure ResidualCertificate {R N r n : ℕ} (A : Fin R → Fin N → ℚ)
    (B : Fin r → Fin n → ℚ) where
  pivotRows : Finset (Fin R)
  pivotCols : Finset (Fin N)
  row : Fin r → Fin R
  col : Fin n → Fin N
  row_injective : Function.Injective row
  col_injective : Function.Injective col
  row_outside : ∀ i, row i ∉ pivotRows
  coefficient : Fin r → Fin R → ℚ
  normalized : ∀ i, coefficient i (row i)=1
  supported : ∀ i j, j ∉ pivotRows → j ≠ row i → coefficient i j=0
  annihilates : ∀ i j, j ∈ pivotCols → rowValue A (coefficient i) j=0
  represents : ∀ i j, B i j=rowValue A (coefficient i) (col j)
  independent : ∀ v : Fin R → ℚ, (∀ i, i ∉ pivotRows → v i=0) →
    (∀ j, j ∈ pivotCols → rowValue A v j=0) → ∀ i, v i=0

namespace ResidualCertificate
variable {R N r n : ℕ} {A : Fin R → Fin N → ℚ} {B : Fin r → Fin n → ℚ}

 theorem decompose (P : ResidualCertificate A B) (i : Fin r) (v : Fin R → ℚ)
    (hv : ∀ j, j ∉ P.pivotRows → j ≠ P.row i → v j=0)
    (hk : ∀ j, j ∈ P.pivotCols → rowValue A v j=0) :
    ∀ j, v j=v (P.row i)*P.coefficient i j := by
  have hzero := P.independent (fun j => v j-v (P.row i)*P.coefficient i j) (by
    intro j hj
    by_cases he : j=P.row i
    · subst j; rw [P.normalized,mul_one,sub_self]
    · rw [hv j hj he,P.supported i j hj he,mul_zero,sub_self]) (by
    intro j hj
    rw [rowValue_sub,hk j hj,P.annihilates i j hj,mul_zero,sub_self])
  intro j
  exact sub_eq_zero.mp (hzero j)

 theorem circuit (P : ResidualCertificate A B) (i : Fin r) :
    IsCircuit (fun c j => A j (P.pivotCols.orderEmbOfFin rfl c)) (P.coefficient i) := by
  intro v hv hk
  refine ⟨v (P.row i),P.decompose i v (fun j hj he => hv j (P.supported i j hj he)) ?_⟩
  intro j hj
  obtain ⟨c,hc⟩ := (P.pivotCols.orderIsoOfFin rfl).surjective ⟨j,hj⟩
  have he : P.pivotCols.orderEmbOfFin rfl c=j := congrArg Subtype.val hc
  simpa only [rowValue,he] using hk c

 def initial (A : Fin R → Fin N → ℚ) : ResidualCertificate A A where
  pivotRows := ∅
  pivotCols := ∅
  row := id
  col := id
  row_injective := Function.injective_id
  col_injective := Function.injective_id
  row_outside _ := (by simp)
  coefficient i j := if j=i then 1 else 0
  normalized _ := ite_eq_left rfl
  supported _ _ _ h := ite_eq_right h
  annihilates _ _ h := by simp at h
  represents i j := by simp [rowValue]
  independent v hv _ i := hv i ((by simp))

 def skip {B : Fin (r+1) → Fin n → ℚ} (P : ResidualCertificate A B) :
    ResidualCertificate A (fun i j => B i.succ j) where
  pivotRows := P.pivotRows
  pivotCols := P.pivotCols
  row i := P.row i.succ
  col := P.col
  col_injective := P.col_injective
  row_injective := P.row_injective.comp (Fin.succ_injective _)
  row_outside i := P.row_outside i.succ
  coefficient i := P.coefficient i.succ
  normalized i := P.normalized i.succ
  supported i := P.supported i.succ
  annihilates i := P.annihilates i.succ
  represents i := P.represents i.succ
  independent := P.independent

variable {B' : Fin (r+1) → Fin (n+1) → ℚ}

 theorem next_row_ne (P : ResidualCertificate A B') (i : Fin r) : P.row i.succ ≠ P.row 0 := by
  intro he
  exact Fin.succ_ne_zero i (P.row_injective he)

 theorem firstCoeff_next (P : ResidualCertificate A B') (i : Fin r) :
    P.coefficient 0 (P.row i.succ)=0 :=
  P.supported 0 _ (P.row_outside _) (P.next_row_ne i)

 def pivot (P : ResidualCertificate A B') (p : Fin (n+1)) (hp : B' 0 p ≠ 0) :
    ResidualCertificate A (residual B' p) where
  pivotRows := insert (P.row 0) P.pivotRows
  pivotCols := insert (P.col p) P.pivotCols
  row i := P.row i.succ
  col j := P.col (p.succAbove j)
  col_injective := P.col_injective.comp p.succAbove_right_injective
  row_injective := P.row_injective.comp (Fin.succ_injective _)
  row_outside i := by simp only [mem_insert,not_or]; exact ⟨P.next_row_ne i,P.row_outside _⟩
  coefficient i j := P.coefficient i.succ j-(B' i.succ p/B' 0 p)*P.coefficient 0 j
  normalized i := by rw [P.normalized,P.firstCoeff_next,mul_zero,sub_zero]
  supported i j hj he := by
    have hj' : j ∉ P.pivotRows := fun h => hj (mem_insert_of_mem h)
    have hj0 : j ≠ P.row 0 := fun h => hj (mem_insert.mpr (Or.inl h))
    rw [P.supported i.succ j hj' he,P.supported 0 j hj' hj0,mul_zero,sub_self]
  annihilates i j hj := by
    rw [rowValue_sub]
    rcases mem_insert.mp hj with he | he
    · subst j
      rw [← P.represents,← P.represents]
      field_simp
      ring
    · rw [P.annihilates _ _ he,P.annihilates _ _ he,mul_zero,sub_self]
  represents i j := by
    rw [rowValue_sub,← P.represents,← P.represents]
    dsimp only [residual]
    ring
  independent v hv hk := by
    have hd := P.decompose 0 v (by
      intro j hj he
      apply hv j
      simpa only [mem_insert,not_or] using And.intro he hj) (by
      intro j hj
      exact hk j (mem_insert_of_mem hj))
    have hve : v=(fun j => v (P.row 0)*P.coefficient 0 j) := funext hd
    have hkey := hk (P.col p) (mem_insert_self _ _)
    rw [hve,rowValue_smul,← P.represents] at hkey
    have hv0 : v (P.row 0)=0 := (mul_eq_zero.mp hkey).resolve_right hp
    intro j
    rw [hd j,hv0,zero_mul]

end ResidualCertificate
end MetricKMedian.Gaussian
end

end OAI
