import OAI.GroupTheory.PolycyclicRecognition.Geometry.GeneralizedLieEigenvectors
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SpectralLieDerivation

namespace OAI

/-! # The semisimple Jordan factor preserves the Lie bracket -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing
variable {L : Type} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

omit [FiniteDimensional ℂ L] in
theorem semisimple_factor_eigenvector_generalized (A S : Module.End ℂ L)
    (hc : Commute A S) (hn : IsNilpotent (A - S))
    {μ : ℂ} {x : L} (hx : x ∈ S.eigenspace μ) :
    x ∈ A.maxGenEigenspace μ := by
  have hxS : x ∈ S.genEigenspace μ ⊤ := S.eigenspace_le_maxGenEigenspace hx
  have hxN : x ∈ (A - S).genEigenspace 0 ⊤ := by
    obtain ⟨k, hk⟩ := hn
    apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
    exact ⟨k, by simp only [zero_smul, sub_zero, hk, LinearMap.zero_apply]⟩
  have hSN : Commute S (A - S) := hc.symm.sub_right (Commute.refl S)
  have h := Module.End.genEigenspace_inf_le_add S (A - S) μ 0 ⊤ ⊤ hSN ⟨hxS, hxN⟩
  have he : S + (A - S) = A := by abel
  simpa only [he, add_zero, top_add] using h

theorem semisimple_jordan_factor_map_lie (A : L →ₗ⁅ℂ⁆ L) (S : Module.End ℂ L)
    (hS : S.IsSemisimple) (hc : Commute A.toLinearMap S)
    (hn : IsNilpotent (A.toLinearMap - S)) (x y : L) :
    S ⁅x, y⁆ = ⁅S x, S y⁆ := by
  let B := (LieAlgebra.ad ℂ L).toLinearMap
  let F : L →ₗ[ℂ] L →ₗ[ℂ] L :=
    { toFun := fun x => S.comp (B x)
      map_add' := by intros; simp [LinearMap.comp_add]
      map_smul' := by intros; simp [LinearMap.comp_smul] }
  let G : L →ₗ[ℂ] L →ₗ[ℂ] L :=
    { toFun := fun x => (B (S x)).comp S
      map_add' := by intros; simp [LinearMap.add_comp]
      map_smul' := by intros; simp [LinearMap.smul_comp] }
  have he : F = G := by
    apply semisimple_bilinear_ext S hS
    intro μ ν u v hu hv
    change S ⁅u, v⁆ = ⁅S u, S v⁆
    have huA := semisimple_factor_eigenvector_generalized A.toLinearMap S hc hn hu
    have hvA := semisimple_factor_eigenvector_generalized A.toLinearMap S hc hn hv
    have hb := lie_mem_maxGenEigenspace A μ ν huA hvA
    have heig := Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
      hb hc hS.isFinitelySemisimple hn
    rw [heig, Module.End.mem_eigenspace_iff.mp hu, Module.End.mem_eigenspace_iff.mp hv,
      smul_lie, lie_smul, smul_smul]
  exact congrArg (fun T : L →ₗ[ℂ] L →ₗ[ℂ] L => T x y) he

end PolycyclicRecognition

end

end OAI
