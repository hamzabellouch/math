import Mathlib

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {V : Type*} [Fintype V]

lemma finite_green_identity (w : V → V → ℝ) (hw : ∀ x y, w x y=w y x)
    (u v : V → ℝ) :
    (∑ x, ∑ y, w x y*(u x-u y)*(v x-v y)) =
      2*∑ x, v x*(∑ y, w x y*(u x-u y)) := by
  have hs : (∑ x, ∑ y, w x y*(u x-u y)*v y) =
      -(∑ x, ∑ y, w x y*(u x-u y)*v x) := by
    rw [Finset.sum_comm,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro y _
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [hw x y]
    ring
  have hsplit : (∑ x, ∑ y, w x y*(u x-u y)*(v x-v y)) =
      (∑ x, ∑ y, w x y*(u x-u y)*v x) -
      (∑ x, ∑ y, w x y*(u x-u y)*v y) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hsplit,hs]
  have he : (∑ x, ∑ y, w x y*(u x-u y)*v x) =
      (∑ x, v x*(∑ y, w x y*(u x-u y))) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [he]
  ring

lemma finite_cutoff_energy_identity (w : V → V → ℝ)
    (hw : ∀ x y, w x y=w y x) (u η : V → ℝ)
    (hh : ∀ x, η x=0 ∨ (∑ y, w x y*(u x-u y))=0) :
    (∑ x, ∑ y, w x y*(η x*u x-η y*u y)^2) =
      (∑ x, ∑ y, w x y*(u x*u y)*(η x-η y)^2) := by
  have hg := finite_green_identity w hw u (fun x => η x^2*u x)
  have hz : (∑ x, ∑ y, w x y*(u x-u y)*(η x^2*u x-η y^2*u y))=0 := by
    rw [hg]
    have hs : (∑ x, (η x^2*u x)*(∑ y, w x y*(u x-u y)))=0 := by
      apply Finset.sum_eq_zero
      intro x _
      rcases hh x with h | h <;> simp [h]
    rw [hs,mul_zero]
  have he : (∑ x, ∑ y, w x y*(u x-u y)*(η x^2*u x-η y^2*u y)) =
      (∑ x, ∑ y, w x y*(η x*u x-η y*u y)^2) -
      (∑ x, ∑ y, w x y*(u x*u y)*(η x-η y)^2) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  exact sub_eq_zero.mp (he.symm.trans hz)

theorem finite_caccioppoli (w : V → V → ℝ)
    (hw : ∀ x y, w x y=w y x) (hw0 : ∀ x y, 0≤w x y)
    (u η : V → ℝ)
    (hh : ∀ x, η x=0 ∨ (∑ y, w x y*(u x-u y))=0) :
    (∑ x, ∑ y, w x y*(η x)^2*(u x-u y)^2) ≤
      4*(∑ x, ∑ y, w x y*(u x)^2*(η x-η y)^2) := by
  let E := ∑ x, ∑ y, w x y*(η x*u x-η y*u y)^2
  let B := ∑ x, ∑ y, w x y*(u x)^2*(η x-η y)^2
  have hswap : (∑ x, ∑ y, w x y*(u y)^2*(η x-η y)^2)=B := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    rw [hw x y]
    ring
  have hE : 2*E≤2*B := by
    rw [show E=(∑ x, ∑ y, w x y*(u x*u y)*(η x-η y)^2) from
      finite_cutoff_energy_identity w hw u η hh]
    have hb : 2*B=B+(∑ x, ∑ y, w x y*(u y)^2*(η x-η y)^2) := by rw [hswap]; ring
    rw [hb]
    unfold B
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    have hhxy := mul_nonneg (hw0 x y) (sq_nonneg (u x-u y))
    have hhxy' := mul_nonneg hhxy (sq_nonneg (η x-η y))
    nlinarith
  have hgrad : (∑ x, ∑ y, w x y*(η x)^2*(u x-u y)^2) ≤
      2*E+2*(∑ x, ∑ y, w x y*(u y)^2*(η x-η y)^2) := by
    unfold E
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    have hsq := mul_nonneg (hw0 x y)
      (sq_nonneg ((η x*u x-η y*u y)+(u y*(η x-η y))))
    nlinarith
  rw [hswap] at hgrad
  change _≤4*B
  linarith

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
