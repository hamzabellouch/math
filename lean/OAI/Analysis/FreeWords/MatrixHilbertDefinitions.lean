import Mathlib

namespace OAI

noncomputable section

namespace KKMatrixHilbert

noncomputable section

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev Amplification (n:ℕ) (H:Type*) := PiLp 2 (fun _:Fin n => H)

def matrixOperator {n:ℕ} (a:Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    Amplification n H →L[ℂ] Amplification n H where
  toFun x := WithLp.toLp 2 (fun i => ∑j,a i j (x j))
  map_add' := by intro x y; ext i; simp [map_add,Finset.sum_add_distrib]
  map_smul' := by intro c x; ext i; simp [map_smul,Finset.smul_sum]
  cont := by
    apply (PiLp.continuous_toLp 2 (fun _:Fin n => H)).comp
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j hj
    exact (a i j).continuous.comp (PiLp.continuous_apply 2 _ j)

omit [CompleteSpace H] in
@[simp] theorem matrixOperator_apply {n:ℕ} (a:Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (x:Amplification n H) (i:Fin n) : matrixOperator a x i=∑j,a i j (x j) := rfl

end

end KKMatrixHilbert
end

end OAI
