import OAI.MathematicalPhysics.Heisenberg.SpinPhysicalOperators

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open TensorUnits
variable {d ℓ : ℕ} {X : Type} [Fintype X] [DecidableEq X]

def realFunctional (τ : State d ℓ) : QuasiLocal d ℓ →ₗ[ℝ] ℝ :=
  (Complex.reCLM.comp (τ.functional.restrictScalars ℝ)).toLinearMap

lemma finiteRepresentation_trace (site : X → Site d) (hinj : Function.Injective site)
    (τ : State d ℓ) (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A))
    (M : Matrix (X → Level ℓ) (X → Level ℓ) ℝ) :
    (τ.functional (finiteRepresentation site hinj M)).re=
      (Fintype.card (X → Level ℓ):ℝ)⁻¹*Matrix.trace M := by
  have ht : ∀ A B,realFunctional τ (A*B)=realFunctional τ (B*A) := fun A B=>congrArg Complex.re (hτ A B)
  have h1 : realFunctional τ 1=1 := by change (τ.functional 1).re=1; rw [τ.normalized]; rfl
  change realFunctional τ (liftAlg (tensorUnits site) (tensorUnits_mul site hinj) (tensorUnits_sum site)
    (Matrix.reindex (functionReindex (Fintype.equivFin X)) (functionReindex (Fintype.equivFin X)) M))=_
  rw [trace_lift _ _ _ _ ht h1]
  have he : Fintype.card (Fin (Fintype.card X) → Level ℓ)=Fintype.card (X → Level ℓ) :=
    Fintype.card_congr (functionReindex (Fintype.equivFin X)).symm
  rw [he]
  congr 1
  exact (functionReindex (Fintype.equivFin X)).symm.sum_comp (fun i=>M i i)

lemma finiteRepresentation_exp (site : X → Site d) (hinj : Function.Injective site)
    (M : Matrix (X → Level ℓ) (X → Level ℓ) ℝ) :
    finiteRepresentation site hinj (NormedSpace.exp M)=NormedSpace.exp (finiteRepresentation site hinj M) :=
  NormedSpace.map_exp (finiteRepresentation (ℓ:=ℓ) site hinj)
    (finiteRepresentation (ℓ:=ℓ) site hinj).toLinearMap.continuous_of_finiteDimensional M

lemma finiteRepresentation_gibbsDensity (site : X → Site d) (hinj : Function.Injective site)
    (H : Matrix (X → Level ℓ) (X → Level ℓ) ℝ) (β : ℝ) :
    gibbsDensity (finiteRepresentation site hinj H) β=
      finiteRepresentation site hinj (NormedSpace.exp ((-β) • H)) := by
  rw [finiteRepresentation_exp,map_smul,gibbsDensity]
  exact congrArg NormedSpace.exp (IsScalarTower.algebraMap_smul ℂ (-β) _)

lemma finiteRepresentation_gibbs_re (site : X → Site d) (hinj : Function.Injective site)
    (τ : State d ℓ) (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A))
    (H A : Matrix (X → Level ℓ) (X → Level ℓ) ℝ)
    (hH : IsSelfAdjoint (finiteRepresentation site hinj H)) (β : ℝ) :
    ((gibbsState τ (finiteRepresentation site hinj H) β).functional
      (finiteRepresentation site hinj A)).re=
      Matrix.trace (NormedSpace.exp ((-β) • H)*A)/Matrix.trace (NormedSpace.exp ((-β) • H)) := by
  rw [gibbsState_apply τ hτ hH,finiteRepresentation_gibbsDensity,←map_mul]
  rw [←Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [finiteRepresentation_trace site hinj τ hτ,finiteRepresentation_trace site hinj τ hτ]
  have hc : (Fintype.card (X → Level ℓ):ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_inv_rev,inv_inv]
  field_simp

end Heisenberg
end
end

end OAI
