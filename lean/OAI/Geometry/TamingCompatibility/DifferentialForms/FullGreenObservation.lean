import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.AmbientKernelLift

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.Variational
open scoped RealInnerProductSpace
variable {V H Z : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

theorem exists_full_green_observation
    (i : V →L[ℝ] H) (hi : Function.Injective i) (D : V →L[ℝ] Z)
    (K : Submodule ℝ H) [CompleteSpace K] (G : H →L[ℝ] V)
    (hgraph : ∀ u, ‖u‖^2 = ‖i u‖^2 + ‖D u‖^2)
    (hker : ∀ k : K, ∃ v : V, i v = k.val ∧ D v = 0)
    (hweak : ∀ f v, ⟪D (G f),D v⟫ = ⟪f-K.starProjection f,i v⟫)
    (horth : ∀ f, i (G f) ∈ Kᗮ) :
    ∃ J : H →L[ℝ] V,
      (∀ f, i (J f) = K.starProjection f) ∧ (∀ f, D (J f) = 0) ∧
      (∀ f, ‖J f‖ ≤ ‖f‖) ∧
      (∀ f v, energy (K.starProjection ∘L i) D v ((G+J) f) = ⟪f,i v⟫) ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (S : Submodule ℝ V) (φ : S →ₗ[ℝ] ℝ) (M : ℝ),
          0 ≤ M → (∀ u, ‖φ u‖ ≤ M*‖u‖) →
          ∃ v : V, ‖v‖ ≤ C*M ∧
            (∀ f : H, ∀ hf : (G+J) f ∈ S, φ ⟨(G+J) f,hf⟩ = ⟪f,i v⟫) ∧
            (∀ w : V, ∀ hw : w-J (i w) ∈ S,
              φ ⟨w-J (i w),hw⟩ = 0 → ⟪D v,D w⟫ = 0) := by
  obtain ⟨J,hJ,hDJ,hnJ⟩ := exists_ambient_kernel_lift i hi D K hgraph hker
  have hfull (f : H) (v : V) : energy (K.starProjection ∘L i) D v ((G+J) f) = ⟪f,i v⟫ := by
    have hz : K.starProjection (i (G f)) = 0 := K.starProjection_apply_eq_zero_iff.mpr (horth f)
    have hp : K.starProjection (i ((G+J) f)) = K.starProjection f := by
      rw [add_apply,map_add,map_add,hz,hJ,zero_add,
        K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem _)]
    rw [energy_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,hp,
      add_apply,map_add,hDJ,add_zero]
    have hd : ⟪D v,D (G f)⟫ = ⟪f-K.starProjection f,i v⟫ :=
      (real_inner_comm _ _).trans (hweak f v)
    have hpi : ⟪K.starProjection (i v),K.starProjection f⟫ = ⟪K.starProjection f,i v⟫ := by
      rw [K.inner_starProjection_left_eq_right,
        K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem _)]
      exact real_inner_comm _ _
    rw [hd,hpi,inner_sub_left]
    ring
  have hc : IsCoercive (energy (K.starProjection ∘L i) D) := projected_energy_coercive i D K G hgraph hweak
  obtain ⟨C,hC,hrep⟩ := exists_uniform_energy_representer _ hc
  refine ⟨J,hJ,hDJ,hnJ,hfull,C,hC,fun S φ M hM hφ => ?_⟩
  obtain ⟨v,hv,hve⟩ := hrep S φ M hM hφ
  refine ⟨v,hv,fun f hf => ?_,?_⟩
  · exact (hve ⟨(G+J) f,hf⟩).symm.trans (hfull f v)
  · intro w hw hφw
    have he := (hve ⟨w-J (i w),hw⟩).trans hφw
    change energy (K.starProjection ∘L i) D v (w-(J ∘L i) w) = 0 at he
    rw [augmented_energy_on_subtracted_test i D K (J ∘L i)
      (fun u => hJ (i u)) (fun u => hDJ (i u))] at he
    exact he
end TamingCompatibility.Variational

end
end

end
end
end

end OAI
