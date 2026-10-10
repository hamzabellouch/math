import OAI.Analysis.IrrationalRotation.Operators.TracialVectorSeparating
import OAI.Analysis.IrrationalRotation.Rotation.RotationTrace

namespace OAI

noncomputable section

namespace Invariant233.Rotation

theorem eq_zero_of_apply_vacuum_eq_zero (θ : ℝ) {A : Hilbert →L[ℂ] Hilbert}
    (hA : A ∈ algebra θ) (hzero : A vacuum = 0) : A = 0 :=
  (vacuum_faithfulTracial θ).eq_zero_of_apply_eq_zero hA hzero

theorem eq_of_apply_vacuum_eq (θ : ℝ) {A B : Hilbert →L[ℂ] Hilbert}
    (hA : A ∈ algebra θ) (hB : B ∈ algebra θ) (heq : A vacuum = B vacuum) : A = B :=
  (vacuum_faithfulTracial θ).eq_of_apply_eq hA hB heq

theorem injective_apply_vacuum (θ : ℝ) :
    Function.Injective (fun A : algebra θ => (A : Hilbert →L[ℂ] Hilbert) vacuum) :=
  (vacuum_faithfulTracial θ).injective_apply

end Invariant233.Rotation

end

end OAI
