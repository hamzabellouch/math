import Mathlib

namespace OAI

/-! Every ordinary bounded higher Hochschild cocycle of a complex von Neumann
algebra is the coboundary of a bounded cochain with values in the same algebra. -/

noncomputable section

namespace BoundedHochschild

abbrev Cochain (M : Type*) [NormedAddCommGroup M] [NormedSpace ℂ M] (n : ℕ) :=
  ContinuousMultilinearMap ℂ (fun _ : Fin n => M) M

def mergeInputs {M : Type*} [Mul M] {n : ℕ}
    (v : Fin (n + 1) → M) (j : Fin n) : Fin n → M :=
  fun i => if i < j then v i.castSucc
    else if i = j then v i.castSucc * v i.succ else v i.succ

noncomputable def differentialValue {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]
    {n : ℕ} (f : Cochain M n) (v : Fin (n + 1) → M) : M :=
  v 0 * f (fun i => v i.succ) +
    ∑ j : Fin n, ((-1 : ℂ) ^ (j.val + 1)) • f (mergeInputs v j) +
    ((-1 : ℂ) ^ (n + 1)) • (f (fun i => v i.castSucc) * v (Fin.last n))

namespace KadisonRingrose

universe u

theorem main_result
    {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (n : ℕ) (f : Cochain M (n + 2))
    (hf : ∀ x : Fin (n + 3) → M, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x : Fin (n + 2) → M,
      differentialValue g x = f x := by
  sorry

end KadisonRingrose
end BoundedHochschild

end

end OAI
