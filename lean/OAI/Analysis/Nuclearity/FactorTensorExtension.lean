import OAI.Analysis.Nuclearity.FactorTensorInjection
import OAI.Analysis.JiangSu.TensorProducts.FaithfulTensorExtension

namespace OAI

/-! The faithful-completion step of Tomiyama's factor-representation argument.
Only the represented left algebra is required to be nuclear. In the ideal
application it is a quotient image, whose nuclearity still requires proof. -/

noncomputable section
open scoped TensorProduct

namespace WeakPureInfiniteness

open KirchbergRordam.GenericRW

universe u v
variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra E]

theorem factor_starTensor_injective (M : VonNeumannAlgebra H)
    (hM : FactorIndependence.IsFactor M)
    (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφM : ∀ a, φ a ∈ M) (hψM : ∀ b, ψ b ∈ M.commutant)
    (hc : ∀ a b, Commute (φ a) (ψ b)) :
    Function.Injective (Pureness.commutingStarTensorHom φ ψ hc) :=
  factor_tensor_lift_injective M hM φ.toAlgHom ψ.toAlgHom hφ hψ hφM hψM hc

theorem factor_tensor_norm_eq (hA : Pureness.IsNuclear.{u,v} A)
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (hf : Function.Injective f)
    (M : VonNeumannAlgebra H) (hM : FactorIndependence.IsFactor M)
    (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφM : ∀ a, φ a ∈ M) (hψM : ∀ b, ψ b ∈ M.commutant)
    (hc : ∀ a b, Commute (φ a) (ψ b)) (z : A ⊗[ℂ] B) :
    ‖f z‖ = ‖Pureness.commutingStarTensorHom φ ψ hc z‖ :=
  hA.faithful_tensor_norm_eq f _ hf
    (factor_starTensor_injective M hM φ ψ hφ hψ hφM hψM hc) z

/-- A faithful factor product extends to the given tensor completion. This
uses nuclearity of the actual represented algebra, not simplicity. -/
theorem exists_factor_tensor_extension (hA : Pureness.IsNuclear.{u,v} A)
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (hf : Function.Injective f) (hd : DenseRange f)
    (M : VonNeumannAlgebra H) (hM : FactorIndependence.IsFactor M)
    (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφM : ∀ a, φ a ∈ M) (hψM : ∀ b, ψ b ∈ M.commutant)
    (hc : ∀ a b, Commute (φ a) (ψ b)) :
    ∃ θ : E →⋆ₐ[ℂ] (H →L[ℂ] H), Isometry θ ∧
      ∀ z, θ (f z) = Pureness.commutingStarTensorHom φ ψ hc z := by
  let g := Pureness.commutingStarTensorHom φ ψ hc
  have hg := factor_starTensor_injective M hM φ ψ hφ hψ hφM hψM hc
  let θ := Pureness.faithfulTensorExtension g hA f hf hd hg
  have hθ (z : A ⊗[ℂ] B) : θ (f z) = g z :=
    Pureness.faithfulTensorExtension_apply g hA f hf hd hg z
  have hθc : Continuous (fun y : E => θ y) := by
    let L := θ.toAlgHom.toLinearMap.mkContinuous 1 (fun y => by
      change ‖θ.toNonUnitalStarAlgHom y‖ ≤ 1 * ‖y‖
      rw [one_mul]
      exact NonUnitalStarAlgHom.norm_apply_le θ.toNonUnitalStarAlgHom y)
    exact L.continuous
  have hn (x : E) : ‖θ x‖ = ‖x‖ := by
    refine hd.induction_on (p := fun y => ‖θ y‖ = ‖y‖) x ?_ ?_
    · exact isClosed_eq (hθc.norm) continuous_norm
    · intro z
      rw [hθ]
      exact (factor_tensor_norm_eq hA f hf M hM φ ψ hφ hψ hφM hψM hc z).symm
  refine ⟨θ, ?_, hθ⟩
  apply isometry_iff_dist_eq.mpr
  intro x y
  simpa only [dist_eq_norm, ← map_sub] using hn (x - y)

end WeakPureInfiniteness

end

end OAI
