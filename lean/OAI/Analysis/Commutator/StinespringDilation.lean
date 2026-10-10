import Mathlib
import OAI.Analysis.Commutator.StinespringRepresentation

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra

open UniformSpace

namespace Kadison.Stinespring

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def elementary (φ : A →CP (H →L[ℂ] H)) (a : A) : H →ₗ[ℂ] PreSpace φ :=
  (toPre φ).toLinearMap.comp (Finsupp.lsingle a)

@[simp] lemma form_elementary (φ : A →CP (H →L[ℂ] H)) (a b : A) (ξ η : H) :
    form φ (elementary φ a ξ) (elementary φ b η)=⟪ξ,φ (star a*b) η⟫_ℂ := by
  classical
  simp [form,elementary,Finsupp.lsingle_apply]

@[simp] lemma leftLinear_elementary (φ : A →CP (H →L[ℂ] H)) (a b : A) (ξ : H) :
    leftLinear φ a (elementary φ b ξ)=elementary φ (a*b) ξ := by
  classical
  simp [leftLinear,elementary,Finsupp.lmapDomain_apply,Finsupp.lsingle_apply]

lemma elementary_one_bound (φ : A →CP (H →L[ℂ] H)) (ξ : H) :
    ‖elementary φ 1 ξ‖≤Real.sqrt ‖φ 1‖*‖ξ‖ := by
  have he : ‖elementary φ 1 ξ‖^2=(⟪ξ,φ 1 ξ⟫_ℂ).re := by
    rw [norm_sq_eq_re_inner (𝕜:=ℂ),inner_def,form_elementary,star_one,one_mul]
    rfl
  have hi := re_inner_le_norm (𝕜:=ℂ) ξ (φ 1 ξ)
  change (⟪ξ,φ 1 ξ⟫_ℂ).re ≤ ‖ξ‖ * ‖φ 1 ξ‖ at hi
  have hn := mul_le_mul_of_nonneg_left ((φ 1).le_opNorm ξ) (norm_nonneg ξ)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg ξ))).mp
  rw [mul_pow,Real.sq_sqrt (norm_nonneg _),he]
  nlinarith

def embedding (φ : A →CP (H →L[ℂ] H)) : H →L[ℂ] Space φ :=
  (Completion.toComplL : PreSpace φ →L[ℂ] Space φ).comp
    ((elementary φ 1).mkContinuous (Real.sqrt ‖φ 1‖) (elementary_one_bound φ))

@[simp] lemma embedding_apply (φ : A →CP (H →L[ℂ] H)) (ξ : H) :
    embedding φ ξ=(elementary φ 1 ξ : Space φ) := rfl

lemma embedding_norm_le (φ : A →CP (H →L[ℂ] H)) : ‖embedding φ‖≤Real.sqrt ‖φ 1‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro ξ
  simpa using elementary_one_bound φ ξ

theorem factorization (φ : A →CP (H →L[ℂ] H)) (a : A) :
    φ a=(embedding φ).adjoint.comp ((representation φ a).comp (embedding φ)) := by
  ext η
  apply ext_inner_left ℂ
  intro ξ
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    embedding_apply,representation_coe,leftLinear_elementary,mul_one,Completion.inner_coe,
    inner_def,form_elementary,star_one,one_mul]

lemma embedding_adjoint_embedding (φ : A →CP (H →L[ℂ] H)) :
    (embedding φ).adjoint.comp (embedding φ)=φ 1 := by
  simpa [ContinuousLinearMap.one_def] using (factorization φ (1 : A)).symm

lemma embedding_norm_sq (φ : A →CP (H →L[ℂ] H)) : ‖embedding φ‖^2=‖φ 1‖ := by
  rw [←embedding_adjoint_embedding,ContinuousLinearMap.norm_adjoint_comp_self]
  ring

end Kadison.Stinespring

end

end
end

end OAI
