import OAI.NumberTheory.JointDickman.Counting.ResidueBoxEnergy
import OAI.NumberTheory.JointDickman.Amplification.IntegratedSampledError

namespace OAI

/-! # Summing local product errors without paying for the number of boxes -/

namespace JointDickman
open Finset

theorem sum_sqrt_product_bound {ι : Type*} (S : Finset ι) (A D : ι → ℝ)
    (hA : ∀ i ∈ S, 0 ≤ A i) (hD : ∀ i ∈ S, 0 ≤ D i) :
    (∑ i ∈ S, Real.sqrt (A i)*Real.sqrt (D i)) ≤
      Real.sqrt (∑ i ∈ S, A i)*Real.sqrt (∑ i ∈ S, D i) := by
  have hh := sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (A i)) (fun i => Real.sqrt (D i))
  have ha : (∑ i ∈ S, Real.sqrt (A i)^2) = ∑ i ∈ S, A i :=
    sum_congr rfl (fun i hi => Real.sq_sqrt (hA i hi))
  have hd : (∑ i ∈ S, Real.sqrt (D i)^2) = ∑ i ∈ S, D i :=
    sum_congr rfl (fun i hi => Real.sq_sqrt (hD i hi))
  rw [ha,hd] at hh
  apply (sq_le_sq₀ (sum_nonneg (fun i _ => by positivity)) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (sum_nonneg hA),Real.sq_sqrt (sum_nonneg hD)]
  exact hh

theorem sum_local_product_errors {ι : Type*} (S : Finset ι)
    (A R T : ι → ℝ) (E : ι → ℂ)
    (hA : ∀ i ∈ S, 0 ≤ A i) (hR : ∀ i ∈ S, 0 ≤ R i) (hT : ∀ i ∈ S, 0 ≤ T i)
    {U V : ℝ} (hV : 0 ≤ V)
    (he : ∀ i ∈ S, ‖E i‖ ≤ U*A i+
      V*(Real.sqrt (R i)*Real.sqrt (A i)+Real.sqrt (A i)*Real.sqrt (T i))) :
    ‖∑ i ∈ S, E i‖ ≤ U*(∑ i ∈ S, A i)+
      V*(Real.sqrt (∑ i ∈ S, R i)*Real.sqrt (∑ i ∈ S, A i)+
        Real.sqrt (∑ i ∈ S, A i)*Real.sqrt (∑ i ∈ S, T i)) := by
  calc
    _ ≤ ∑ i ∈ S, ‖E i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, (U*A i+V*(Real.sqrt (R i)*Real.sqrt (A i)+Real.sqrt (A i)*Real.sqrt (T i))) :=
      sum_le_sum he
    _ = U*(∑ i ∈ S, A i)+V*((∑ i ∈ S, Real.sqrt (R i)*Real.sqrt (A i))+
        (∑ i ∈ S, Real.sqrt (A i)*Real.sqrt (T i))) := by
      simp only [sum_add_distrib,mul_sum,mul_add]
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left
      (add_le_add (sum_sqrt_product_bound S R A hR hA) (sum_sqrt_product_bound S A T hA hT)) hV) _

theorem sum_local_product_errors_of_totals {ι : Type*} (S : Finset ι)
    (A R T : ι → ℝ) (E : ι → ℂ)
    (hA : ∀ i ∈ S, 0 ≤ A i) (hR : ∀ i ∈ S, 0 ≤ R i) (hT : ∀ i ∈ S, 0 ≤ T i)
    {U V D r : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hD : 0 ≤ D) (_hr : 0 ≤ r)
    (hAt : ∑ i ∈ S, A i ≤ D) (hRt : ∑ i ∈ S, R i ≤ D*r)
    (hTt : ∑ i ∈ S, T i ≤ D*r)
    (he : ∀ i ∈ S, ‖E i‖ ≤ U*A i+
      V*(Real.sqrt (R i)*Real.sqrt (A i)+Real.sqrt (A i)*Real.sqrt (T i))) :
    ‖∑ i ∈ S, E i‖ ≤ D*(U+2*V*Real.sqrt r) := by
  have hsa := Real.sqrt_le_sqrt hAt
  have hsr := Real.sqrt_le_sqrt hRt
  have hst := Real.sqrt_le_sqrt hTt
  have hprod : Real.sqrt (D*r)*Real.sqrt D = D*Real.sqrt r := by
    rw [Real.sqrt_mul hD]
    calc
      _ = (Real.sqrt D)^2*Real.sqrt r := by ring
      _ = _ := by rw [Real.sq_sqrt hD]
  calc
    _ ≤ U*(∑ i ∈ S, A i)+
        V*(Real.sqrt (∑ i ∈ S, R i)*Real.sqrt (∑ i ∈ S, A i)+
          Real.sqrt (∑ i ∈ S, A i)*Real.sqrt (∑ i ∈ S, T i)) :=
      sum_local_product_errors S A R T E hA hR hT hV he
    _ ≤ U*D+V*(Real.sqrt (D*r)*Real.sqrt D+Real.sqrt D*Real.sqrt (D*r)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hAt hU)
        (mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul hsr hsa (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (mul_le_mul hsa hst (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) hV)
    _ = _ := by rw [mul_comm (Real.sqrt D),hprod]; ring

theorem sum_sqrt_product_of_totals {ι : Type*} (S : Finset ι) (A R : ι → ℝ)
    (hA : ∀ i ∈ S, 0 ≤ A i) (hR : ∀ i ∈ S, 0 ≤ R i)
    {D r : ℝ} (hD : 0 ≤ D) (hAt : ∑ i ∈ S, A i ≤ D)
    (hRt : ∑ i ∈ S, R i ≤ D*r) :
    (∑ i ∈ S, Real.sqrt (A i)*Real.sqrt (R i)) ≤ D*Real.sqrt r := by
  calc
    _ ≤ Real.sqrt (∑ i ∈ S, A i)*Real.sqrt (∑ i ∈ S, R i) :=
      sum_sqrt_product_bound S A R hA hR
    _ ≤ Real.sqrt D*Real.sqrt (D*r) :=
      mul_le_mul (Real.sqrt_le_sqrt hAt) (Real.sqrt_le_sqrt hRt)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hD]
      calc
        _ = (Real.sqrt D)^2*Real.sqrt r := by ring
        _ = _ := by rw [Real.sq_sqrt hD]

end JointDickman

end OAI
