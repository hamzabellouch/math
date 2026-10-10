import OAI.Probability.InvariantIsing.Cavity.CavityCompletion
import OAI.Probability.InvariantIsing.Cavity.CavityCompressionLimitGeometry

namespace OAI

/-! The fixed limiting complement required by the physical cavity bound
exists for every positive finite spectral law. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

theorem cavity_limiting_complement_exists {m n d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (ρ : Fin m → ℝ)
    (hρ : ∀ a, 0≤ρ a) (hsum : ∑ a, ρ a=1) :
    ∃ B : Matrix (Fin (d+n)) (Fin d) ℝ,
      B.transpose*B=1 ∧ (cavityReindexedStack e (fun a => ρ a • 1)).transpose*B=0 := by
  let E := cavityReindexedStack e (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ))
  have hE : E.transpose*E=1 := by
    ext i j
    have he := Equiv.sum_comp e.symm (fun k =>
      cavityLimitingStack (n := n) ρ k i*cavityLimitingStack (n := n) ρ k j)
    have hg := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j)
      (cavityLimitingStack_gram (n := n) ρ hρ hsum)
    simpa only [E, Matrix.mul_apply, Matrix.transpose_apply, cavityReindexedStack,
      cavitySpectralStack_scalar_eq ρ hρ] using he.trans hg
  exact cavity_frame_completion E hE

end InvariantIsing

end

end OAI
