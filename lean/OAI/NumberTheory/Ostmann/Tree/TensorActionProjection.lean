import OAI.NumberTheory.Ostmann.Tree.IndependentMajorants
import OAI.NumberTheory.Ostmann.Tree.TensorProjection

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators
open Ostmann.Tree.Density
variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,MulAction Fˣ (A i)]
local instance tensorActionFintype : Fintype (MulChar F ℂ) := Fintype.ofFinite _

def actionProjection (W : ∀ i,A i → ℂ) (x : ∀ i,A i) : ℂ :=
  (Fintype.card Fˣ:ℂ)⁻¹*∑ z : Fˣ,∏ i,W i (z • x i)

def actionCoefficient (W : ∀ i,A i → ℂ) (i : I) (ρ : MulChar F ℂ) (x : A i) : ℂ :=
  mellin (fun z : Fˣ => W i (z • x)) ρ

def coordinateActionEquiv (t : I → Fˣ) : (∀ i,A i) ≃ (∀ i,A i) :=
  Equiv.piCongrRight (fun i => MulAction.toPerm (t i))

omit [DecidableEq I] [∀ i,Fintype (A i)] in
theorem tensorSignedProjection_action (W : ∀ i,A i → ℂ) (x : ∀ i,A i) (t : I → Fˣ) :
    tensorSignedProjection (fun i z => W i (z • x i)) (fun _ => true) t =
      actionProjection (F := F) W (coordinateActionEquiv t x) := by
  unfold tensorSignedProjection actionProjection
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.prod_congr rfl
  intro i _
  simp only [signedUnit,ite_true,coordinateActionEquiv,Equiv.piCongrRight_apply,
    mul_smul]
  change W i (t i • (z • x i))=W i (z • (t i • x i))
  simp only [smul_smul]
  rw [mul_comm]

theorem actionProjection_energy (W : ∀ i,A i → ℂ) :
    average (fun x : ∀ i,A i => ‖actionProjection (F := F) W x‖^2) =
      ∑ ρ : I → MulChar F ℂ,if (∏ i,ρ i)=1 then
        ∏ i,average (fun x : A i => ‖actionCoefficient W i (ρ i) x‖^2) else 0 := by
  classical
  have hN : (Fintype.card (I → Fˣ):ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he (t : I → Fˣ) :
      average (fun x : ∀ i,A i =>
        ‖tensorSignedProjection (fun i z => W i (z • x i)) (fun _ => true) t‖^2) =
      average (fun x : ∀ i,A i => ‖actionProjection (F := F) W x‖^2) := by
    simp_rw [tensorSignedProjection_action]
    unfold average
    congr 1
    exact (coordinateActionEquiv t).bijective.sum_comp (fun x => ‖actionProjection (F := F) W x‖^2)
  calc
    _ = average (fun t : I → Fˣ => average (fun x : ∀ i,A i =>
        ‖tensorSignedProjection (fun i z => W i (z • x i)) (fun _ => true) t‖^2)) := by
      simp_rw [he]
      simp only [average,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      exact (inv_mul_cancel_left₀ hN _).symm
    _ = average (fun x : ∀ i,A i => average (fun t : I → Fˣ =>
        ‖tensorSignedProjection (fun i z => W i (z • x i)) (fun _ => true) t‖^2)) := by
      simp only [average,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = average (Ostmann.Tree.constrainedMajorant (fun _ : I => Equiv.refl (MulChar F ℂ))
        (fun i ρ x => ‖actionCoefficient W i ρ x‖^2)) := by
      congr 1
      funext x
      rw [show average (fun t : I → Fˣ =>
        ‖tensorSignedProjection (fun i z => W i (z • x i)) (fun _ => true) t‖^2) = _ from
        tensorSignedProjection_parseval (fun i z => W i (z • x i)) (fun _ => true)]
      simp only [tensorConstraint,signedCharacter,ite_true,Ostmann.Tree.constrainedMajorant,
        Equiv.refl_apply,actionCoefficient]
      congr 1
    _ = _ := Ostmann.Tree.constrainedMajorant_average _ _

end
end Ostmann.FiniteField

end OAI
