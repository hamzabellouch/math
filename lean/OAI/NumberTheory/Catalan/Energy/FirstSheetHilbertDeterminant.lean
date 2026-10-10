import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Determinant

namespace OAI


noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem firstSheet_det_norm_le_pow {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (L : V →ₗ[ℂ] V) {C : ℝ} (hL : ∀ v, ‖L v‖ ≤ C * ‖v‖) :
    ‖LinearMap.det L‖ ≤ C ^ Module.finrank ℂ V := by
  classical
  let b := stdOrthonormalBasis ℂ V
  let f : Fin (Module.finrank ℂ V) → V := fun i => L (b i)
  have hd : Module.finrank ℂ V = Fintype.card (Fin (Module.finrank ℂ V)) := by simp
  let c := InnerProductSpace.gramSchmidtOrthonormalBasis hd f
  have hdet : ‖c.toBasis.det f‖ = ‖LinearMap.det L‖ := by
    change ‖c.toBasis.det (L ∘ b)‖ = _
    rw [Module.Basis.det_comp, norm_mul,
      OrthonormalBasis.det_to_matrix_orthonormalBasis, mul_one]
  have hprod : ‖c.toBasis.det f‖ =
      ∏ i, ‖inner ℂ (c i) (f i)‖ := by
    simpa only [norm_prod] using congrArg (fun z : ℂ => ‖z‖)
      (InnerProductSpace.gramSchmidtOrthonormalBasis_det hd f)
  calc
    ‖LinearMap.det L‖ = ∏ i, ‖inner ℂ (c i) (f i)‖ := hdet.symm.trans hprod
    _ ≤ ∏ _i : Fin (Module.finrank ℂ V), C := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      calc
        ‖inner ℂ (c i) (f i)‖ ≤ ‖c i‖ * ‖f i‖ := norm_inner_le_norm _ _
        _ = ‖L (b i)‖ := by simp only [c.norm_eq_one, one_mul, f]
        _ ≤ C := by simpa only [b.norm_eq_one, mul_one] using hL (b i)
    _ = C ^ Module.finrank ℂ V := by simp

end InternalCatalan

end

end OAI
