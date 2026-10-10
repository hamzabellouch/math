import OAI.MathematicalPhysics.Heisenberg.MatrixUnitTrace

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open TensorUnits
variable {d ℓ : ℕ} {X : Type} [Fintype X] [DecidableEq X]

def tensorUnits (site : X → Site d) (a b : Fin (Fintype.card X) → Level ℓ) : QuasiLocal d ℓ :=
  system (fun i=>localUnit d ℓ (site ((Fintype.equivFin X).symm i))) a b

omit [DecidableEq X] in
lemma tensorUnits_mul (site : X → Site d) (hinj : Function.Injective site)
    (a b c e : Fin (Fintype.card X) → Level ℓ) :
    tensorUnits site a b*tensorUnits site c e=if b=c then tensorUnits site a e else 0 := by
  apply system_mul _ (fun i=>localUnit_mul_same d ℓ _)
  intro i j hij a b c e
  exact localUnits_commute (fun h=>hij ((Fintype.equivFin X).symm.injective (hinj h))) a b c e

omit [DecidableEq X] in
lemma tensorUnits_sum (site : X → Site d) :
    ∑ a : Fin (Fintype.card X) → Level ℓ,tensorUnits site a a=1 :=
  system_diagonal_sum ℝ _ (fun _=>localUnit_diagonal_sum d ℓ _)

def finiteRepresentation (site : X → Site d) (hinj : Function.Injective site) :
    Matrix (X → Level ℓ) (X → Level ℓ) ℝ →ₐ[ℝ] QuasiLocal d ℓ :=
  (liftAlg (tensorUnits site) (tensorUnits_mul site hinj) (tensorUnits_sum site)).comp
    (Matrix.reindexAlgEquiv ℝ ℝ (functionReindex (Fintype.equivFin X))).toAlgHom

lemma finiteRepresentation_onsite (site : X → Site d) (hinj : Function.Injective site)
    (x : X) (M : Matrix (Level ℓ) (Level ℓ) ℝ) :
    finiteRepresentation site hinj (TensorMatrix.onsite x M)=
      liftLinear (localUnit d ℓ (site x)) M := by
  change liftLinear (system (fun i=>localUnit d ℓ (site ((Fintype.equivFin X).symm i))))
    (Matrix.reindex (functionReindex (Fintype.equivFin X)) (functionReindex (Fintype.equivFin X))
      (TensorMatrix.onsite x M))=_
  rw [reindex_onsite,lift_onsiteFin _ (fun i=>localUnit_diagonal_sum d ℓ _)]
  simp only [Equiv.symm_apply_apply]

lemma finiteRepresentation_z (site : X → Site d) (hinj : Function.Injective site) (x : X) :
    finiteRepresentation site hinj (TensorMatrix.onsite x (SpinSlots.physicalZ ℓ))=spinZ d ℓ (site x) := by
  rw [finiteRepresentation_onsite]
  change (∑ a,∑ b,Matrix.diagonal (fun k : Level ℓ=>(k:ℝ)-(ℓ:ℝ)/2) a b • localUnit d ℓ (site x) a b)=_
  simp only [Matrix.diagonal_apply,ite_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a _
  exact (IsScalarTower.algebraMap_smul ℂ ((a:ℝ)-(ℓ:ℝ)/2) (localUnit d ℓ (site x) a a)).symm

end Heisenberg
end
end

end OAI
