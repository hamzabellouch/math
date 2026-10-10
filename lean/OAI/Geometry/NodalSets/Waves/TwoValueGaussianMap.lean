import OAI.Geometry.NodalSets.Coefficients.TwoPointCoefficientEnergy
import OAI.Geometry.NodalSets.Waves.FiniteGaussianMap

namespace OAI

namespace Yau.Geometry
open Yau.Probability MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma pairJetMap_two_inner (z w : ι → ℂ) (v : EuclideanSpace ℝ (Fin 2))
    (a : ι × Fin 2 → ℝ) :
    ⟪v,pairJetMap ![z,w] (WithLp.toLp 2 a)⟫ =
      pairLinearSum (fun i ↦ (v 0:ℂ)*z i+(v 1:ℂ)*w i) a := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,star_trivial,Fin.sum_univ_two,pairJetMap_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,pairLinearSum_real_combination]
  ring

lemma pairJetMap_two_energy (z w : ι → ℂ) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖(pairJetMap ![z,w]).adjoint v‖^2 =
      ∑ i, ‖(v 0:ℂ)*z i+(v 1:ℂ)*w i‖^2 := by
  rw [← variance_gaussianMap_inner]
  simp_rw [pairJetMap_two_inner]
  exact variance_pairLinearSum _

lemma two_point_energy_upper (z w : ι → ℂ) (M : ℝ)
    (hz : ∑ i, ‖z i‖^2 ≤ M) (hw : ∑ i, ‖w i‖^2 ≤ M) (u v : ℝ) :
    (∑ i, ‖(u:ℂ)*z i+(v:ℂ)*w i‖^2) ≤ 2*M*(u^2+v^2) := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦
    complex_norm_add_sq_bound ((u:ℂ)*z i) ((v:ℂ)*w i))
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Finset.sum_add_distrib,← Finset.mul_sum] at hh
  have hz' := mul_le_mul_of_nonneg_left hz (sq_nonneg u)
  have hw' := mul_le_mul_of_nonneg_left hw (sq_nonneg v)
  nlinarith

end
end Yau.Geometry

end OAI
