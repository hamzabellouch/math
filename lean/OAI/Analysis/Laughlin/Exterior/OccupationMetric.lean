import OAI.Analysis.Laughlin.Asymptotics.LocalDiagonalLimit
import OAI.Analysis.Laughlin.Exterior.OccupationDiagonal

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology

theorem exteriorScaling_coordinate (Q : ℕ) (d : Fin (Q+1) → ℂ)
    (x : Space Q) (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (exteriorScaling Q d x) A =
      (∏ i ∈ A, d i)*(occupationBasis Q).repr x A := by
  have h : ((occupationBasis Q).coord A).comp (exteriorScaling Q d).toLinearMap =
      (∏ i ∈ A, d i) • (occupationBasis Q).coord A := by
    apply (occupationBasis Q).ext
    intro B
    change (occupationBasis Q).repr (exteriorScaling Q d (occupationBasis Q B)) A =
      (∏ i ∈ A, d i)*(occupationBasis Q).repr (occupationBasis Q B) A
    rw [exteriorScaling_occupation_entry]
    by_cases hBA : B = A
    · subst B
      simp
    · simp [Module.Basis.repr_self, hBA]
  exact LinearMap.congr_fun h x

noncomputable def occupationNormSq (Q : ℕ) (x : Space Q) : ℝ :=
  ∑ A : Finset (Fin (Q+1)), ‖(occupationBasis Q).repr x A‖^2

theorem occupationNormSq_nonneg (Q : ℕ) (x : Space Q) : 0 ≤ occupationNormSq Q x := by
  unfold occupationNormSq
  positivity

theorem localScaling_error_quadratic (L Q : ℕ) (x : Space L) :
    occupationNormSq L (exteriorScaling L (fun i => (modeFactor Q i.val : ℂ)) x - x) ≤
      (localDiagonalError L Q)^2 * occupationNormSq L x := by
  have he (A : Finset (Fin (L+1))) :
      (occupationBasis L).repr (exteriorScaling L (fun i => (modeFactor Q i.val : ℂ)) x - x) A =
        ((localDiagonals L Q A - 1 : ℝ) : ℂ)*(occupationBasis L).repr x A := by
    rw [map_sub, Finsupp.sub_apply, exteriorScaling_coordinate]
    unfold localDiagonals
    push_cast
    ring
  unfold occupationNormSq
  simp_rw [he]
  exact localDiagonalError_quadratic L Q (fun A => (occupationBasis L).repr x A)

end Laughlin.Fock

end OAI
