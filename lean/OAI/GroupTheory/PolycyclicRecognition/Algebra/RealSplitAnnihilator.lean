import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexTriangularPolynomial
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularPrimary

namespace OAI

/-! # A real annihilating polynomial from a complex flag with real diagonal -/

noncomputable section
namespace PolycyclicRecognition
open Module
open scoped TensorProduct

theorem real_split_annihilator_of_complex_triangular
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} (A : Module.End ℝ V) (b : Basis (Fin n) ℂ (ℂ ⊗[ℝ] V))
    (hu : (LinearMap.toMatrix b b (A.baseChange ℂ)).IsUpperTriangular)
    (hr : ∀ i, (LinearMap.toMatrix b b (A.baseChange ℂ) i i).im = 0) :
    ∃ S : Finset ℝ,
      Polynomial.aeval A ((∏ a ∈ S, (Polynomial.X - Polynomial.C a)) ^ n) = 0 := by
  classical
  let M := LinearMap.toMatrix b b (A.baseChange ℂ)
  let d : Fin n → ℝ := fun i => (M i i).re
  let S := Finset.univ.image d
  let Q : Polynomial ℝ := ∏ a ∈ S, (Polynomial.X - Polynomial.C a)
  have hd (i : Fin n) : M i i = (d i : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (hr i).trans (by simp)
  have hmap : Q.map (algebraMap ℝ ℂ) =
      ∏ a ∈ S, (Polynomial.X - Polynomial.C (a : ℂ)) := by
    simp only [Q,Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
    rfl
  have hdiv : M.charpoly ∣ (Q.map (algebraMap ℝ ℂ)) ^ n := by
    rw [Matrix.charpoly_of_isUpperTriangular M hu]
    have hh := prod_dvd_pow_card Finset.univ
      (fun i : Fin n => Polynomial.X - Polynomial.C (M i i))
      (Q.map (algebraMap ℝ ℂ)) (by
        intro i _
        rw [hd,hmap]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_image_of_mem d (Finset.mem_univ i)))
    simpa only [Finset.card_univ,Fintype.card_fin] using hh
  have hm : Polynomial.aeval M ((Q.map (algebraMap ℝ ℂ)) ^ n) = 0 := by
    obtain ⟨p,hp⟩ := hdiv
    rw [hp,map_mul,Matrix.aeval_self_charpoly,zero_mul]
  have hc : Polynomial.aeval (A.baseChange ℂ) ((Q.map (algebraMap ℝ ℂ)) ^ n) = 0 := by
    apply (LinearMap.toMatrixAlgEquiv b).injective
    rw [← Polynomial.aeval_algHom_apply,map_zero]
    exact hm
  have ht : (Polynomial.aeval A (Q ^ n)).baseChange ℂ = 0 := by
    change (Module.End.baseChangeHom ℝ ℂ V) (Polynomial.aeval A (Q ^ n)) = 0
    rw [← Polynomial.aeval_algHom_apply,
      Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq ℝ ℂ _).symm]
    change Polynomial.aeval (A.baseChange ℂ) ((Q ^ n).map (algebraMap ℝ ℂ)) = 0
    simpa only [Polynomial.map_pow] using hc
  refine ⟨S,?_⟩
  apply LinearMap.ext
  intro v
  apply (Module.FaithfullyFlat.one_tmul_eq_zero_iff ℝ V (A := ℂ) _).mp
  exact (LinearMap.congr_fun ht ((1 : ℂ) ⊗ₜ[ℝ] v))

end PolycyclicRecognition

end

end OAI
