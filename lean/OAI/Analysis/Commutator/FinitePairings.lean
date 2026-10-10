import Mathlib
import OAI.Analysis.Commutator.CoefficientForm

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.PreHilbert

lemma word_orthonormal (E F : PreHilbert) (Ω : E) (hΩ : ‖Ω‖ = 1)
    {ι : Type*} (v : ι → F) (hv : Orthonormal ℂ v) (n : ℕ) :
    Orthonormal ℂ (fun b : Fin n → ι => word E F n Ω (fun i => v (b i))) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro b c
  rw [inner_word, inner_self_eq_norm_sq_to_K, hΩ]
  have hh := orthonormal_iff_ite.mp (pure_orthonormal F v hv n) b c
  simpa [inner_pure] using hh

end Kadison.PreHilbert
end

end OAI
