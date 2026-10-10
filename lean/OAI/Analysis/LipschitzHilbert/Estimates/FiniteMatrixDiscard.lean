import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeMatrixBound

namespace OAI

/-! A finite matrix restricted to two retained index sets differs from
the full matrix by at most the product bounds with one discarded factor. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

private theorem finite_product_sum {ι ν : Type*} (I : Finset ι) (J : Finset ν)
    (a : ι → ℝ) (b : ν → ℝ) :
    (∑ i∈I, ∑ j∈J, a i*b j)=(∑ i∈I, a i)*(∑ j∈J, b j) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

theorem finite_matrix_discard_bound {ι ν : Type*} (I : Finset ι) (J : Finset ν)
    (p : ι → Prop) (q : ν → Prop) [DecidablePred p] [DecidablePred q]
    (a : ι → ℝ) (b : ν → ℝ) (B : ι → ν → ℂ) (C : ℝ)
    (hC : 0≤C) (ha : ∀ i∈I, 0≤a i) (hb : ∀ j∈J, 0≤b j)
    (hB : ∀ i∈I, ∀ j∈J, ‖B i j‖≤C*a i*b j) :
    ‖(∑ i∈I, ∑ j∈J, B i j)-(∑ i∈I.filter p, ∑ j∈J.filter q, B i j)‖≤
      C*((∑ i∈I.filter (fun i => ¬p i), a i)*(∑ j∈J, b j)+
        (∑ i∈I, a i)*(∑ j∈J.filter (fun j => ¬q j), b j)) := by
  have heq : (∑ i∈I, ∑ j∈J, B i j)-(∑ i∈I.filter p, ∑ j∈J.filter q, B i j)=
      ∑ i∈I, ∑ j∈J, if p i ∧ q j then 0 else B i j := by
    simp only [Finset.sum_filter]
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : p i
    · simp only [hp,ite_true]
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hq : q j <;> simp [hq]
    · simp [hp]
  rw [heq]
  calc
    _≤∑ i∈I, ∑ j∈J, ‖if p i ∧ q j then 0 else B i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _≤∑ i∈I, ∑ j∈J, C*((if p i then 0 else a i)*b j+a i*(if q j then 0 else b j)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hh := hB i hi j hj
      have hn : 0≤C*a i*b j := mul_nonneg (mul_nonneg hC (ha i hi)) (hb j hj)
      by_cases hp : p i <;> by_cases hq : q j <;> simp [hp,hq] <;> nlinarith
    _=C*(∑ i∈I, ∑ j∈J, (if p i then 0 else a i)*b j)+
        C*(∑ i∈I, ∑ j∈J, a i*(if q j then 0 else b j)) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_add]
    _=_ := by
      rw [finite_product_sum,finite_product_sum]
      simp only [Finset.sum_filter,ite_not]
      ring

end LipschitzHilbert

end

end OAI
