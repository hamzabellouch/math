import Mathlib
import OAI.Analysis.Commutator.CyclicImplementationUnconditional

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.CyclicSpatial

open ReducingRepresentation

variable {A K H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
  (j : K →ₗᵢ[ℂ] H) (hj : ∀ a x, j (σ a x)=ρ a (j x))

local instance : NormedAddCommGroup (K →L[ℂ] H) := ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℂ (K →L[ℂ] H) := ContinuousLinearMap.toNormedSpace

include hj in
omit [PartialOrder A] [StarOrderedRing A] in
lemma range_invariant (a : A) (x : H) (hx : x∈LinearMap.range j.toLinearMap) :
    ρ a x∈LinearMap.range j.toLinearMap := by
  obtain ⟨y,rfl⟩ := hx
  exact ⟨σ a y,hj a y⟩

include hj in
theorem exists_embedded_cyclic_intertwiner (M : VonNeumannAlgebra H)
    (hρ : Function.Injective ρ) (hrange : Set.range ρ=(M : Set (H →L[ℂ] H)))
    (G : K →L[ℂ] H) (Ω : K) (hΩ : DenseRange (fun a : A => σ a Ω))
    {ε : ℝ} (hε : 0≤ε)
    (hδ : ∀ a : A, ‖G.comp (σ a)-(ρ a).comp G‖≤ε*‖a‖) :
    ∃ T : K →L[ℂ] H, (∀ a : A,T.comp (σ a)=(ρ a).comp T) ∧ ‖G-T‖≤16*ε := by
  let J := LinearMap.range j.toLinearMap
  let e : K ≃ₗᵢ[ℂ] J := j.equivRange
  let : CompleteSpace J := e.symm.toIsometryEquiv.completeSpace
  let : NormedAddCommGroup (J →L[ℂ] H) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℂ (J →L[ℂ] H) := ContinuousLinearMap.toNormedSpace
  let hinv := range_invariant σ ρ j hj
  let ρJ := restrict ρ J hinv
  have he (a : A) (x : K) : e (σ a x)=ρJ a (e x) := by
    apply Subtype.ext
    exact hj a x
  have hes (a : A) (x : J) : e.symm (ρJ a x)=σ a (e.symm x) := by
    apply e.injective
    rw [LinearIsometryEquiv.apply_symm_apply,he,LinearIsometryEquiv.apply_symm_apply]
  have hΩJ : DenseRange (fun a : A => ρJ a (e Ω)) := by
    have hh := e.surjective.denseRange.comp hΩ e.continuous
    have heq : (fun a : A => ρJ a (e Ω)) = e ∘ (fun a : A => σ a Ω) :=
      funext (fun a => (he a Ω).symm)
    rw [heq]
    exact hh
  let GJ := G.comp e.symm.toLinearIsometry.toContinuousLinearMap
  have hed (a : A) : delta ρ J hinv GJ a=
      (G.comp (σ a)-(ρ a).comp G).comp e.symm.toLinearIsometry.toContinuousLinearMap := by
    ext x
    change G (e.symm (ρJ a x))-ρ a (G (e.symm x))=G (σ a (e.symm x))-ρ a (G (e.symm x))
    rw [hes]
  have hd : ‖delta ρ J hinv GJ‖≤ε := by
    apply ContinuousLinearMap.opNorm_le_bound _ hε
    intro a
    rw [hed]
    calc
      _ ≤ ‖G.comp (σ a)-(ρ a).comp G‖*‖e.symm.toLinearIsometry.toContinuousLinearMap‖ := opNorm_comp_le _ _
      _ ≤ (ε*‖a‖)*1 := mul_le_mul (hδ a) e.symm.toLinearIsometry.norm_toContinuousLinearMap_le
        (ContinuousLinearMap.opNorm_nonneg _) (mul_nonneg hε (norm_nonneg _))
      _ = _ := mul_one _
  obtain ⟨T,hT,hn⟩ := exists_cyclic_intertwiner_unconditional ρ J hinv M hρ hrange GJ (e Ω) hΩJ
  refine ⟨T.comp e.toLinearIsometry.toContinuousLinearMap,?_,?_⟩
  · intro a
    ext x
    change T (e (σ a x))=ρ a (T (e x))
    rw [he]
    exact congrArg (fun R : J →L[ℂ] H => R (e x)) (hT a)
  · have heq : G-T.comp e.toLinearIsometry.toContinuousLinearMap=(GJ-T).comp e.toLinearIsometry.toContinuousLinearMap := by
      ext x
      change G x-T (e x)=G (e.symm (e x))-T (e x)
      rw [LinearIsometryEquiv.symm_apply_apply]
    rw [heq]
    calc
      _ ≤ ‖GJ-T‖*‖e.toLinearIsometry.toContinuousLinearMap‖ := opNorm_comp_le _ _
      _ ≤ (16*‖delta ρ J hinv GJ‖)*1 := mul_le_mul hn e.toLinearIsometry.norm_toContinuousLinearMap_le
        (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
      _ ≤ 16*ε := by nlinarith

end Kadison.CyclicSpatial

end

end
end

end OAI
