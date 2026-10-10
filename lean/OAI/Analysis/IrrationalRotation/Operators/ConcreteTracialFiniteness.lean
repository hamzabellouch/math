import OAI.Analysis.IrrationalRotation.Operators.TracialFiniteness
import OAI.Analysis.IrrationalRotation.Rotation.RotationTrace
import OAI.Analysis.IrrationalRotation.Product.ProductTracialVector

namespace OAI

noncomputable section

namespace Invariant233.Rotation

theorem mem_unitary_of_isometry_mem_algebra (θ : ℝ)
    {v : Hilbert →L[ℂ] Hilbert} (hvm : v ∈ algebra θ) (hv : star v * v = 1) :
    v ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  (vacuum_faithfulTracial θ).mem_unitary_of_star_mul_eq_one hvm hv

theorem mem_unitary_of_coisometry_mem_algebra (θ : ℝ)
    {v : Hilbert →L[ℂ] Hilbert} (hvm : v ∈ algebra θ) (hv : v * star v = 1) :
    v ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  (vacuum_faithfulTracial θ).mem_unitary_of_mul_star_eq_one hvm hv

end Invariant233.Rotation

namespace Invariant233.ProductModel

theorem mem_unitary_of_isometry_mem_factor (θ : ℕ → ℝ)
    {v : Hilbert →L[ℂ] Hilbert} (hvm : v ∈ factor θ) (hv : star v * v = 1) :
    v ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  (traceVector_faithfulTracial θ).mem_unitary_of_star_mul_eq_one hvm hv

theorem mem_unitary_of_coisometry_mem_factor (θ : ℕ → ℝ)
    {v : Hilbert →L[ℂ] Hilbert} (hvm : v ∈ factor θ) (hv : v * star v = 1) :
    v ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  (traceVector_faithfulTracial θ).mem_unitary_of_mul_star_eq_one hvm hv

end Invariant233.ProductModel

end

end OAI
