import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionKernel

namespace OAI

namespace ProjectionComparison

open Set

variable {V E : Type*} [Fintype V]

lemma projection_firm (S : System V E) (b v₀ v₁ h₀ h₁ : V → ℝ)
    (hp₀ : IsProjection S b v₀ h₀) (hp₁ : IsProjection S b v₁ h₁) :
    (∑x,((v₁ x-v₀ x)-(h₁ x-h₀ x))^2)≤(∑x,(v₁ x-v₀ x)^2)-(∑x,(h₁ x-h₀ x)^2) := by
  have e₀ := variational S b v₀ h₀ hp₀ h₁ hp₁.1
  have e₁ := variational S b v₁ h₁ hp₁ h₀ hp₀.1
  have hi : (∑x,((v₁ x-v₀ x)-(h₁ x-h₀ x))^2)-((∑x,(v₁ x-v₀ x)^2)-(∑x,(h₁ x-h₀ x)^2))=
      -2*((∑x,(h₀ x-v₀ x)*(h₁ x-h₀ x))+(∑x,(h₁ x-v₁ x)*(h₀ x-h₁ x))) := by
    simp only [← Finset.sum_sub_distrib,← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx;ring
  linarith

lemma faceAverage_selfadjoint (S : System V E) (F : Finset E) (d e : V → ℝ) :
    (∑x,d x*faceAverage S F e x)=∑x,faceAverage S F d x*e x := by
  classical
  simp only [faceAverage_eq_sum,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [faceKernel_symm S F y x]
  ring

lemma faceAverage_energy_identity (S : System V E) (F : Finset E) (d : V → ℝ) :
    (∑x,(d x-faceAverage S F d x)^2)=(∑x,d x^2)-(∑x,(faceAverage S F d x)^2) := by
  have h := faceAverage_selfadjoint S F d (faceAverage S F d)
  simp only [faceAverage_idempotent,← sq] at h
  have hi : (∑x,(d x-faceAverage S F d x)^2)-((∑x,d x^2)-(∑x,(faceAverage S F d x)^2))=
      2*((∑x,(faceAverage S F d x)^2)-(∑x,d x*faceAverage S F d x)) := by
    simp only [← Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx;ring
  linarith

end ProjectionComparison

end OAI
