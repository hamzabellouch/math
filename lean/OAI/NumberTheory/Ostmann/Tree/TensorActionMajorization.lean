import OAI.NumberTheory.Ostmann.Tree.TensorActionProjection

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators
open Ostmann.Tree.Density
variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,MulAction Fˣ (A i)]
local instance tensorActionMajorizationFintype : Fintype (MulChar F ℂ) := Fintype.ofFinite _

omit [Fintype I] [DecidableEq I] in
theorem actionCoefficient_energy_nonneg (W : ∀ i,A i → ℂ) (i : I) (ρ : MulChar F ℂ) :
    0≤average (fun x : A i => ‖actionCoefficient W i ρ x‖^2) :=
  mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem actionProjection_energy_le (W : ∀ i,A i → ℂ)
    (B : I → MulChar F ℂ → ℝ)
    (hB : ∀ i ρ,average (fun x : A i => ‖actionCoefficient W i ρ x‖^2)≤B i ρ) :
    average (fun x : ∀ i,A i => ‖actionProjection (F:=F) W x‖^2) ≤
      ∑ ρ : I → MulChar F ℂ,if (∏ i,ρ i)=1 then ∏ i,B i (ρ i) else 0 := by
  classical
  rw [actionProjection_energy]
  apply Finset.sum_le_sum
  intro ρ _
  split_ifs
  · exact Finset.prod_le_prod₀ (fun i _ => actionCoefficient_energy_nonneg W i (ρ i))
      (fun i _ => hB i (ρ i))
  · exact le_rfl

end
end Ostmann.FiniteField

end OAI
