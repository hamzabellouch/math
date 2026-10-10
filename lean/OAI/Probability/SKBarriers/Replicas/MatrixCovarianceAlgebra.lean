import Mathlib

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

section FiniteGram
variable {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]

theorem finite_gram_cross_covariance (X : I → A → ℝ) (Y : I → B → ℝ) :
    (∑ i, ∑ j, (∑ a, X i a*X j a)*(∑ b, Y i b*Y j b))=
      ∑ a, ∑ b, (∑ i, X i a*Y i b)^2 := by
  classical
  simp only [pow_two,Fintype.sum_mul_sum]
  calc
    _ = ∑ i, ∑ j, ∑ a, ∑ b, (X i a*Y i b)*(X j a*Y j b) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      ring
    _ = ∑ i, ∑ a, ∑ j, ∑ b, (X i a*Y i b)*(X j a*Y j b) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ b, (X i a*Y i b)*(X j a*Y j b) := Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, (X i a*Y i b)*(X j a*Y j b) := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro i _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl; intro a _
      exact Finset.sum_comm

theorem finite_linear_covariance (F : I → A → ℝ) (x y : A → ℝ) :
    (∑ i, (∑ a, F i a*x a)*(∑ b, F i b*y b))=
      ∑ a, ∑ b, (∑ i, F i a*F i b)*x a*y b := by
  classical
  simp only [Fintype.sum_mul_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  ring
end FiniteGram

def replicaCrossOverlap (N d : ℕ) (X Y : Fin N → Fin d → ℝ) (a b : Fin d) : ℝ :=
  (∑ i, X i a*Y i b)/(N:ℝ)

def matrixPairFeature (N d : ℕ) (β : ℝ) (X : Fin N → Fin d → ℝ)
    (p : Fin N × Fin N) : ℝ :=
  (β/Real.sqrt (2*(N:ℝ)))*∑ a, X p.1 a*X p.2 a

theorem matrixPairFeature_covariance {N d : ℕ} (hN : 0<N) (β : ℝ)
    (X Y : Fin N → Fin d → ℝ) :
    (∑ p : Fin N × Fin N, matrixPairFeature N d β X p*matrixPairFeature N d β Y p)=
      ((N:ℝ)*β^2/2)*∑ a, ∑ b, (replicaCrossOverlap N d X Y a b)^2 := by
  have hNr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have hs : (Real.sqrt (2*(N:ℝ)))^2=2*(N:ℝ) := Real.sq_sqrt (by positivity)
  have hf : (β/Real.sqrt (2*(N:ℝ)))^2=β^2/(2*(N:ℝ)) := by rw [div_pow,hs]
  simp only [matrixPairFeature,Fintype.sum_prod_type]
  have he (i j : Fin N) :
      (β/Real.sqrt (2*(N:ℝ))*(∑ a, X i a*X j a))*(β/Real.sqrt (2*(N:ℝ))*(∑ b, Y i b*Y j b))=
        (β^2/(2*(N:ℝ)))*((∑ a, X i a*X j a)*(∑ b, Y i b*Y j b)) := by rw [← hf]; ring
  simp_rw [he]
  simp_rw [← Finset.mul_sum]
  rw [finite_gram_cross_covariance]
  simp only [replicaCrossOverlap,div_pow,← Finset.sum_div]
  field_simp

def matrixFieldFeature (N d r : ℕ) (β : ℝ) (B : Fin r → Fin d → ℝ)
    (X : Fin N → Fin d → ℝ) (p : Fin N × Fin r) : ℝ :=
  β*∑ a, B p.2 a*X p.1 a

def factorCovariance (d r : ℕ) (B : Fin r → Fin d → ℝ) (a b : Fin d) : ℝ :=
  ∑ u, B u a*B u b

theorem matrixFieldFeature_covariance {N d r : ℕ} (β : ℝ) (B : Fin r → Fin d → ℝ)
    (X Y : Fin N → Fin d → ℝ) :
    (∑ p : Fin N × Fin r, matrixFieldFeature N d r β B X p*matrixFieldFeature N d r β B Y p)=
      ((N:ℝ)*β^2)*∑ a, ∑ b, factorCovariance d r B a b*replicaCrossOverlap N d X Y a b := by
  by_cases hN : N=0
  · subst N
    simp [matrixFieldFeature]
  have hNr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN
  simp only [matrixFieldFeature,Fintype.sum_prod_type]
  have he (i : Fin N) (u : Fin r) :
      (β*(∑ a, B u a*X i a))*(β*(∑ b, B u b*Y i b))=
        β^2*((∑ a, B u a*X i a)*(∑ b, B u b*Y i b)) := by ring
  simp_rw [he,← Finset.mul_sum,finite_linear_covariance]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun (i : Fin N) (b : Fin d) => _)]
  simp only [replicaCrossOverlap,factorCovariance,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  field_simp
  simp only [Finset.mul_sum,mul_assoc]
  simp_rw [← Finset.mul_sum]
  ring

end SK.Analytic

end
end

end OAI
