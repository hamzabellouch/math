import Mathlib
import OAI.LinearAlgebra.MatrixFields.Entropy.StageCLaw

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

def statisticLaw (d : ℚ) (k : Fin 5) (i : Fin 6) : ℚ :=
  if k.val = 2 then
    if i = 2 then 1 - d else if i = 3 then d else 0
  else if i = singletonSlot k.val then 1 else 0

def statisticComplement (k : Fin 5) : Fin 5 := ⟨4 - k.val, by omega⟩

theorem statisticLaw_complement (d : ℚ) (k : Fin 5) (i : Fin 6) :
    statisticLaw d k (kappa i) = statisticLaw d (statisticComplement k) i := by
  fin_cases k <;> fin_cases i <;> rfl

theorem statisticLaw_outside_support (d : ℚ) (k : Fin 5) (i : Fin 6)
    (h : statisticWeight i ≠ k.val) : statisticLaw d k i = 0 := by
  fin_cases k <;> fin_cases i
  all_goals first | rfl | exact False.elim (h (by decide))

theorem littleLaw_eq_statisticLaw (t u : Shape) (w : Fin 3) (hw : u w < 5) (i : Fin 6) :
    littleLaw t u w i = statisticLaw (binaryParameter t u) ⟨u w, hw⟩ i := rfl

theorem littleLaw_outside_support (t u : Shape) (w : Fin 3) (hw : u w < 5) (i : Fin 6)
    (h : statisticWeight i ≠ u w) : littleLaw t u w i = 0 :=
  statisticLaw_outside_support _ ⟨u w, hw⟩ i h

theorem littleLaw_complement (t u : Shape) (w v : Fin 3)
    (hw : u w < 5) (hv : u v < 5) (hsum : u w + u v = 4) (i : Fin 6) :
    littleLaw t u w (kappa i) = littleLaw t u v i := by
  rw [littleLaw_eq_statisticLaw t u w hw, littleLaw_eq_statisticLaw t u v hv]
  have hk : (⟨u v, hv⟩ : Fin 5) = statisticComplement ⟨u w, hw⟩ := by
    apply Fin.ext
    simp only [statisticComplement]
    omega
  rw [hk]
  exact statisticLaw_complement _ _ _

theorem child_statistic_weight_bounded : ∀ t ∈ positiveSecond, ∀ u ∈ below t,
    ∀ w : Fin 3, u w < 5 := by decide +kernel

theorem pair_complement_involution (i j : Fin 6) :
    (kappa (kappa i), kappa (kappa j)) = (i, j) := by simp [kappa_involution]

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
