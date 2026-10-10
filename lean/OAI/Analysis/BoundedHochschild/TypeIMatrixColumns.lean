import OAI.Analysis.BoundedHochschild.HomogeneousTypeIPrimitives
import OAI.Analysis.BoundedHochschild.TypeICentralDecomposition
import OAI.Analysis.BoundedHochschild.PartialIsoCornerEquivalence

namespace OAI

/-! Homogeneous matrix systems from equivalent orthogonal abelian projections. -/

noncomputable section

open scoped BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison HochschildMatrixSystems

variable {M : Type*} [CStarAlgebra M] {n : ℕ} {p : M}

def matrixSystemOfColumns (v : Fin n → PartialIso M)
    (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (hs : ∑ i, (v i).final = 1) : MatrixSystem M n where
  entry i j := (v i : M) * star (v j : M)
  star_entry i j := by simp only [star_mul, star_star]
  entry_mul i j k l := by
    classical
    by_cases h : j = k
    · subst k
      rw [ite_eq_left rfl]
      calc
        _ = (v i : M) * (v j).initial * star (v l : M) := by
          simp only [PartialIso.initial, mul_assoc]
        _ = (v i : M) * (v i).initial * star (v l : M) := by rw [hi, hi]
        _ = _ := by rw [(v i).mul_initial]
    · rw [ite_eq_right h]
      calc
        _ = (v i : M) * (star (v j : M) * (v k : M)) * star (v l : M) := by
          simp only [mul_assoc]
        _ = 0 := by rw [PartialIso.star_mul_eq_zero_of_final_orthogonal (ho j k h),
          mul_zero, zero_mul]
  sum_diagonal := hs

@[simp] lemma matrixSystemOfColumns_diagonal (v : Fin n → PartialIso M)
    (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (hs : ∑ i, (v i).final = 1) (i : Fin n) :
    (matrixSystemOfColumns v hi ho hs).entry i i = (v i).final := rfl

variable [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma matrixSystemOfColumns_abelian (v : Fin n → PartialIso M)
    (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (hs : ∑ i, (v i).final = 1)
    (hp : IsStarProjection p) (hpa : PopaTypeII.AbelianProjection hp) (i : Fin n) :
    FinitePathMain.AbelianProjection ((matrixSystemOfColumns v hi ho hs).entry i i) := by
  have hinit : PopaTypeII.AbelianProjection (v i).initial_proj := by
    simpa only [hi] using hpa
  exact finitePath_abelian_of_popa (v i).final_proj (abelianProjection_partialIso (v i) hinit)

end KadisonRingrose
end BoundedHochschild

end

end OAI
