import OAI.Combinatorics.EditApproximation.Binary.BinaryWideChildWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandTailWork

namespace OAI

/-! The representative constructor executes the balanced child grids
before materializing the Cartesian product and evaluating its scores. -/

namespace EditApproximation
namespace BinaryFraction

def preparedRepresentativeWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (center : TargetInterval ny) (sourceLength b P : ℕ) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction) : List (Fin M → TargetInterval ny) × ℕ :=
  let wide := wideActionGridWithWork M parent center b P
  let result := representativeFromActionsWithWork parent center sourceLength b tau theta child
    (wide.1.map Vector.get)
  (result.1, wide.2 + result.2 + wide.1.length + 1)

theorem preparedRepresentativeWithWork_eq {nx ny M : ℕ} (parent : TargetInterval nx)
    (center : TargetInterval ny) (sourceLength b P : ℕ) (hP : 0 < P)
    (tau theta : BinaryFraction) (child : Fin M → TargetInterval ny → BinaryFraction) :
    (preparedRepresentativeWithWork parent center sourceLength b P tau theta child).1 =
      (representativeBandWithWork parent center sourceLength b P tau theta child).1 := by
  simp only [preparedRepresentativeWithWork, representativeBandWithWork,
    wideActionGridWithWork_value M parent center b P hP, materializedWideActionsWithWork_value]

@[simp] theorem preparedRepresentativeWithWork_value {α : Type*} (source target : List α)
    {M : ℕ} (parent : TargetInterval source.length) (center : TargetInterval target.length)
    (b P : ℕ) (hP : 0 < P) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval target.length → BinaryFraction) :
    (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau theta child).1 =
      representativeBandActions source target parent center b P tau.value theta.value
        (fun i q => (child i q).value) := by
  rw [preparedRepresentativeWithWork_eq _ _ _ _ _ hP]
  exact representativeBandWithWork_value source target parent center b P tau theta child

end BinaryFraction
end EditApproximation

end OAI
