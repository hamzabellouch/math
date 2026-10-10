import Mathlib
import OAI.Probability.SKGap.Localization.ScalarVariance
import OAI.Probability.SKGap.Stability.ConditionalMean

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
variable {n : ℕ}

def conditionalVariance (P : Spin n→ℝ) (x : Spin n) (i : Fin n) : ℝ :=
  1-(conditionalMean P x i)^2

def varianceEnergy (P : Spin n→ℝ) (f : Observables n) : ℝ :=
  ∑ x,P x*∑ i,conditionalVariance P x i*(halfDiff i f x)^2

lemma conditionalVariance_nonneg (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (x : Spin n) (i : Fin n) : 0≤conditionalVariance P x i := by
  have h:=conditionalMean_abs_le P hP x i
  have hh:=pow_le_pow_left₀ (abs_nonneg (conditionalMean P x i)) h 2
  simpa only [sq_abs,one_pow,conditionalVariance,sub_nonneg] using hh

lemma conditionalVariance_le_one (P : Spin n→ℝ) (x : Spin n) (i : Fin n) :
    conditionalVariance P x i≤1 := by dsimp [conditionalVariance]; nlinarith [sq_nonneg (conditionalMean P x i)]

lemma varianceEnergy_nonneg (P : Spin n→ℝ) (hP : ∀ x,0≤P x) (f : Observables n) :
    0≤varianceEnergy P f := by
  exact Finset.sum_nonneg (fun x _=>mul_nonneg (hP x)
    (Finset.sum_nonneg (fun i _=>mul_nonneg (conditionalVariance_nonneg P hP x i) (sq_nonneg _))))

lemma residual_product_identity (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (G : Observables n) (U : VectorFields n) :
    (∑ x,P x*G x*∑ i,(spin x i-conditionalMean P x i)*U x i)=
    (∑ x,P x*G x*∑ i,conditionalVariance P x i*halfDiff i (fun y=>U y i) x)+
    ∑ x,P x*∑ i,conditionalVariance P x i*halfDiff i G x*
      (U x i-2*spin x i*halfDiff i (fun y=>U y i) x) := by
  have H (i : Fin n):=law_integration_by_parts_variance P hP i (fun x=>G x*U x i)
  simp_rw [halfDiff_mul] at H
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  rw [Finset.sum_comm,Finset.sum_comm (f:=fun x i=>
    P x*G x*(conditionalVariance P x i*halfDiff i (fun y=>U y i) x)+
    P x*(conditionalVariance P x i*halfDiff i G x*
      (U x i-2*spin x i*halfDiff i (fun y=>U y i) x)))]
  apply Finset.sum_congr rfl
  intro i _
  convert H i using 1
  · apply Finset.sum_congr rfl; intro x _; ring
  · apply Finset.sum_congr rfl; intro x _; dsimp [conditionalVariance]; ring

lemma diagonal_reflected_bound (U : VectorFields n) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B)
    (hD : ∀ x,∑ i,|halfDiff i (fun y=>U y i) x|≤A)
    (hU : ∀ x,∑ i,(U x i)^2≤B^2) (x : Spin n) :
    (∑ i,(U x i-2*spin x i*halfDiff i (fun y=>U y i) x)^2)≤(2*B+4*A)^2 := by
  have hd : (∑ i,(halfDiff i (fun y=>U y i) x)^2)≤A^2 := by
    have h:=Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ)
      (f:=fun i=>|halfDiff i (fun y=>U y i) x|) (fun i _=>abs_nonneg _)
    simp only [sq_abs] at h
    exact h.trans (pow_le_pow_left₀ (Finset.sum_nonneg (fun i _=>abs_nonneg _)) (hD x) 2)
  calc
    _ ≤ ∑ i,(2*(U x i)^2+8*(halfDiff i (fun y=>U y i) x)^2) := by
      apply Finset.sum_le_sum
      intro i _
      have hs:=spin_sq x i
      have he : (spin x i*halfDiff i (fun y=>U y i) x)^2=
          (halfDiff i (fun y=>U y i) x)^2 := by rw [mul_pow,hs,one_mul]
      nlinarith only [sq_nonneg (U x i+2*spin x i*halfDiff i (fun y=>U y i) x),he]
    _ = 2*(∑ i,(U x i)^2)+8*(∑ i,(halfDiff i (fun y=>U y i) x)^2) := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    _ ≤ (2*B+4*A)^2 := by nlinarith [hU x,mul_nonneg hA hB]

lemma weighted_residual_derivative_bound (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (G : Observables n) (U : VectorFields n) {A : ℝ}
    (hD : ∀ x,∑ i,|halfDiff i (fun y=>U y i) x|≤A) :
    |∑ x,P x*G x*∑ i,conditionalVariance P x i*halfDiff i (fun y=>U y i) x|≤
      A*(∑ x,P x*|G x|) := by
  calc
    _ ≤ ∑ x,|P x*G x*∑ i,conditionalVariance P x i*halfDiff i (fun y=>U y i) x| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ x,P x*|G x| *A := by
      apply Finset.sum_le_sum; intro x _
      rw [abs_mul,abs_mul,abs_of_nonneg (hP x)]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hP x) (abs_nonneg _))
      calc
        _ ≤ ∑ i,|conditionalVariance P x i*halfDiff i (fun y=>U y i) x| :=
          Finset.abs_sum_le_sum_abs ..
        _ ≤ ∑ i,|halfDiff i (fun y=>U y i) x| := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_mul,abs_of_nonneg (conditionalVariance_nonneg P hP x i)]
          exact mul_le_of_le_one_left (abs_nonneg _) (conditionalVariance_le_one P x i)
        _ ≤ A := hD x
    _ = _ := by rw [←Finset.sum_mul,mul_comm]

lemma energy_pair_bound (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (hPsum : ∑ x,P x=1) (f : Observables n) (V : VectorFields n) {C : ℝ}
    (hC : 0≤C) (hV : ∀ x,∑ i,(V x i)^2≤C^2) :
    |∑ x,P x*∑ i,conditionalVariance P x i*halfDiff i f x*V x i|≤
      C*Real.sqrt (varianceEnergy P f) := by
  have H:=weighted_cauchy_sq (fun a : Spin n×Fin n=>P a.1*conditionalVariance P a.1 a.2)
    (fun a=>halfDiff a.2 f a.1) (fun a=>V a.1 a.2)
    (fun a=>mul_nonneg (hP _) (conditionalVariance_nonneg P hP _ _))
  simp only [Fintype.sum_prod_type,mul_assoc,←Finset.mul_sum] at H
  have hv : (∑ x,P x*∑ i,conditionalVariance P x i*(V x i)^2)≤C^2 := by
    calc
      _ ≤ ∑ x,P x*C^2 := by
        apply Finset.sum_le_sum; intro x _
        apply mul_le_mul_of_nonneg_left _ (hP x)
        exact (Finset.sum_le_sum (fun i _=>mul_le_of_le_one_left (sq_nonneg _) (conditionalVariance_le_one P x i))).trans (hV x)
      _ = C^2 := by rw [←Finset.sum_mul,hPsum,one_mul]
  have hn:=varianceEnergy_nonneg P hP f
  have ht:=H.trans (mul_le_mul_of_nonneg_left hv hn)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).1
  rw [sq_abs,mul_pow,Real.sq_sqrt hn]
  simpa only [varianceEnergy,mul_assoc,mul_comm,mul_left_comm] using ht

theorem signed_weak_residual_base (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (hPsum : ∑ x,P x=1) (G : Observables n) (U : VectorFields n) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B)
    (hD : ∀ x,∑ i,|halfDiff i (fun y=>U y i) x|≤A)
    (hU : ∀ x,∑ i,(U x i)^2≤B^2) :
    |∑ x,P x*G x*∑ i,(spin x i-conditionalMean P x i)*U x i|≤
      A*(∑ x,P x*|G x|)+(2*B+4*A)*Real.sqrt (varianceEnergy P G) := by
  rw [residual_product_identity P hP G U]
  exact (abs_add_le _ _).trans (add_le_add (weighted_residual_derivative_bound P hP G U hD)
    (energy_pair_bound P hP hPsum G _ (by positivity) (diagonal_reflected_bound U hA hB hD hU)))

lemma coordinate_abs_le_of_square_sum (V : VectorFields n) {C : ℝ}
    (hC : 0≤C) (hV : ∀ x,∑ i,(V x i)^2≤C^2) (x : Spin n) (i : Fin n) :
    |V x i|≤C := by
  apply (sq_le_sq₀ (abs_nonneg _) hC).1
  rw [sq_abs]
  exact (Finset.single_le_sum (fun k _=>sq_nonneg (V x k)) (Finset.mem_univ i)).trans (hV x)

lemma energy_cross_square_bound (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (f : Observables n) (V : VectorFields n) {C : ℝ}
    (hC : 0≤C) (hV : ∀ x,∑ i,(V x i)^2≤C^2) :
    |2*(∑ x,P x*∑ i,conditionalVariance P x i*f x*halfDiff i f x*V x i)|≤
      C*((∑ x,P x*(f x)^2)+varianceEnergy P f) := by
  have H:=weighted_cauchy_sq (fun a : Spin n×Fin n=>P a.1*conditionalVariance P a.1 a.2)
    (fun a=>halfDiff a.2 f a.1) (fun a=>f a.1*V a.1 a.2)
    (fun a=>mul_nonneg (hP _) (conditionalVariance_nonneg P hP _ _))
  simp only [Fintype.sum_prod_type,mul_assoc,←Finset.mul_sum] at H
  have hv : (∑ x,P x*∑ i,conditionalVariance P x i*(f x*V x i)^2)≤
      C^2*(∑ x,P x*(f x)^2) := by
    calc
      _ ≤ ∑ x,P x*((f x)^2*C^2) := by
        apply Finset.sum_le_sum; intro x _
        apply mul_le_mul_of_nonneg_left _ (hP x)
        have he : (∑ i,conditionalVariance P x i*(f x*V x i)^2)=
            (f x)^2*(∑ i,conditionalVariance P x i*(V x i)^2) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
        rw [he]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact (Finset.sum_le_sum (fun i _=>mul_le_of_le_one_left (sq_nonneg _) (conditionalVariance_le_one P x i))).trans (hV x)
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
  have hn:=varianceEnergy_nonneg P hP f
  have hz : 0≤∑ x,P x*(f x)^2 := Finset.sum_nonneg (fun x _=>mul_nonneg (hP x) (sq_nonneg _))
  have he : (∑ x,P x*∑ i,conditionalVariance P x i*(halfDiff i f x*(f x*V x i)))=
      ∑ x,P x*∑ i,conditionalVariance P x i*f x*halfDiff i f x*V x i := by
    apply Finset.sum_congr rfl; intro x _; congr 1
    apply Finset.sum_congr rfl; intro i _; ring
  rw [he] at H
  have ht:=H.trans (mul_le_mul_of_nonneg_left hv hn)
  change _≤varianceEnergy P f*(C^2*(∑ x,P x*(f x)^2)) at ht
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (add_nonneg hz hn))).1
  rw [sq_abs]
  nlinarith [mul_nonneg (sq_nonneg C) (sq_nonneg ((∑ x,P x*(f x)^2)-varianceEnergy P f))]

lemma energy_square_coefficient_bound (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (f : Observables n) (V : VectorFields n) {C : ℝ}
    (hC : 0≤C) (hV : ∀ x,∑ i,(V x i)^2≤C^2) :
    |∑ x,P x*∑ i,conditionalVariance P x i*spin x i*(halfDiff i f x)^2*V x i|≤
      C*varianceEnergy P f := by
  calc
    _ ≤ ∑ x,|P x*∑ i,conditionalVariance P x i*spin x i*(halfDiff i f x)^2*V x i| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ x,P x*∑ i,C*(conditionalVariance P x i*(halfDiff i f x)^2) := by
      apply Finset.sum_le_sum; intro x _
      rw [abs_mul,abs_of_nonneg (hP x)]
      apply mul_le_mul_of_nonneg_left _ (hP x)
      apply (Finset.abs_sum_le_sum_abs ..).trans
      apply Finset.sum_le_sum; intro i _
      simp only [abs_mul,abs_of_nonneg (conditionalVariance_nonneg P hP x i),abs_spin_eq_one,
        mul_one,abs_of_nonneg (sq_nonneg (halfDiff i f x))]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (coordinate_abs_le_of_square_sum V hC hV x i)
        (mul_nonneg (conditionalVariance_nonneg P hP x i) (sq_nonneg (halfDiff i f x)))
    _ = _ := by
      simp only [varianceEnergy,Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro i _; ring

lemma halfDiff_square (i : Fin n) (f : Observables n) (x : Spin n) :
    halfDiff i (fun y=>(f y)^2) x=2*f x*halfDiff i f x-2*spin x i*(halfDiff i f x)^2 := by
  simp only [pow_two,halfDiff_mul]; ring

theorem square_weak_residual_base (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (f : Observables n) (U : VectorFields n) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B)
    (hD : ∀ x,∑ i,|halfDiff i (fun y=>U y i) x|≤A)
    (hU : ∀ x,∑ i,(U x i)^2≤B^2) :
    |∑ x,P x*(f x)^2*∑ i,(spin x i-conditionalMean P x i)*U x i|≤
      (13*A+6*B)*((∑ x,P x*(f x)^2)+varianceEnergy P f) := by
  let V : VectorFields n:=fun x i=>U x i-2*spin x i*halfDiff i (fun y=>U y i) x
  let C:=2*B+4*A
  have hC : 0≤C := by dsimp [C]; positivity
  have hV : ∀ x,∑ i,(V x i)^2≤C^2 := diagonal_reflected_bound U hA hB hD hU
  rw [residual_product_identity P hP (fun x=>(f x)^2) U]
  have hd:=weighted_residual_derivative_bound P hP (fun x=>(f x)^2) U hD
  simp only [abs_pow,sq_abs] at hd
  have he : (∑ x,P x*∑ i,conditionalVariance P x i*halfDiff i (fun y=>(f y)^2) x*V x i)=
      2*(∑ x,P x*∑ i,conditionalVariance P x i*f x*halfDiff i f x*V x i)-
      2*(∑ x,P x*∑ i,conditionalVariance P x i*spin x i*(halfDiff i f x)^2*V x i) := by
    simp only [halfDiff_square,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro i _; ring
  change |_+(∑ x,P x*∑ i,conditionalVariance P x i*halfDiff i (fun y=>(f y)^2) x*V x i)|≤_
  rw [he]
  have ht:=energy_cross_square_bound P hP f V hC hV
  have hs:=energy_square_coefficient_bound P hP f V hC hV
  have hr:=abs_sub
    (2*(∑ x,P x*∑ i,conditionalVariance P x i*f x*halfDiff i f x*V x i))
    (2*(∑ x,P x*∑ i,conditionalVariance P x i*spin x i*(halfDiff i f x)^2*V x i))
  simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hr ht
  have hu:=abs_add_le
    (∑ x,P x*(f x)^2*∑ i,conditionalVariance P x i*halfDiff i (fun y=>U y i) x)
    (2*(∑ x,P x*∑ i,conditionalVariance P x i*f x*halfDiff i f x*V x i)-
      2*(∑ x,P x*∑ i,conditionalVariance P x i*spin x i*(halfDiff i f x)^2*V x i))
  have hn:=varianceEnergy_nonneg P hP f
  have hz : 0≤∑ x,P x*(f x)^2 := Finset.sum_nonneg (fun x _=>mul_nonneg (hP x) (sq_nonneg _))
  dsimp only [C] at *
  nlinarith [mul_nonneg hA hn,mul_nonneg (add_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hB)
    (mul_nonneg (by norm_num : (0:ℝ)≤4) hA)) hz]

lemma varianceEnergy_gibbs (J : Interaction n)
    (hJ : ∀ i k,J i k=J k i) (hd : ∀ i,J i i=0) (f : Observables n) :
    varianceEnergy (gibbs J) f=dirichlet J f f := by
  simp only [varianceEnergy,conditionalVariance,conditionalMean_gibbs J hJ hd,
    dirichlet,gibbsExpectation,siteVariance,pow_two,mul_assoc]

lemma sum_abs_mul_le_of_squares {ι : Type*} [Fintype ι] (u v : ι→ℝ)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hu : ∑ i,(u i)^2≤A^2) (hv : ∑ i,(v i)^2≤B^2) :
    (∑ i,|u i*v i|)≤A*B := by
  have H:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i=>|u i|) (fun i=>|v i|)
  simp only [sq_abs,←abs_mul] at H
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun i _=>abs_nonneg _)) (mul_nonneg hA hB)).1
  rw [mul_pow]
  exact H.trans (mul_le_mul hu hv (Finset.sum_nonneg (fun i _=>sq_nonneg _)) (sq_nonneg _))

lemma multiplier_vector_bounds (U : VectorFields n) (θ : Observables n) {A B H L : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hH : 0≤H) (hL : 0≤L)
    (hD : ∀ x,∑ i,|halfDiff i (fun y=>U y i) x|≤A)
    (hU : ∀ x,∑ i,(U x i)^2≤B^2)
    (hθ : ∀ x,|θ x|≤H) (hdθ : ∀ x,∑ i,(halfDiff i θ x)^2≤L^2) :
    (∀ x,∑ i,|halfDiff i (fun y=>θ y*U y i) x|≤H*A+(2*B+4*A)*L) ∧
    (∀ x,∑ i,(θ x*U x i)^2≤(H*B)^2) := by
  constructor
  · intro x
    have hc:=sum_abs_mul_le_of_squares
      (fun i=>U x i-2*spin x i*halfDiff i (fun y=>U y i) x)
      (fun i=>halfDiff i θ x) (show 0≤2*B+4*A by positivity) hL
      (diagonal_reflected_bound U hA hB hD hU x) (hdθ x)
    have ht : (∑ i,|θ x*halfDiff i (fun y=>U y i) x|)≤H*A := by
      simp only [abs_mul,←Finset.mul_sum]
      exact mul_le_mul (hθ x) (hD x) (Finset.sum_nonneg (fun i _=>abs_nonneg _)) hH
    calc
      _ ≤ ∑ i,(|θ x*halfDiff i (fun y=>U y i) x|+
          |(U x i-2*spin x i*halfDiff i (fun y=>U y i) x)*halfDiff i θ x|) := by
        apply Finset.sum_le_sum; intro i _
        rw [halfDiff_mul]
        convert abs_add_le (θ x*halfDiff i (fun y=>U y i) x)
          ((U x i-2*spin x i*halfDiff i (fun y=>U y i) x)*halfDiff i θ x) using 1
        ring_nf
      _ ≤ _ := by rw [Finset.sum_add_distrib]; exact add_le_add ht hc
  · intro x
    simp only [mul_pow,←Finset.mul_sum]
    exact mul_le_mul (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (θ x)) (hθ x) 2)
      (hU x) (Finset.sum_nonneg (fun i _=>sq_nonneg _)) (sq_nonneg _)

theorem square_multiplier_weak_residual_base (P : Spin n→ℝ) (hP : ∀ x,0≤P x)
    (f θ : Observables n) (U : VectorFields n) {A B H L : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hH : 0≤H) (hL : 0≤L)
    (hD : ∀ x,∑ i,|halfDiff i (fun y=>U y i) x|≤A)
    (hU : ∀ x,∑ i,(U x i)^2≤B^2)
    (hθ : ∀ x,|θ x|≤H) (hdθ : ∀ x,∑ i,(halfDiff i θ x)^2≤L^2) :
    |∑ x,P x*(f x)^2*θ x*∑ i,(spin x i-conditionalMean P x i)*U x i|≤
      (13*(H*A+(2*B+4*A)*L)+6*(H*B))*
        ((∑ x,P x*(f x)^2)+varianceEnergy P f) := by
  obtain ⟨hD',hU'⟩:=multiplier_vector_bounds U θ hA hB hH hL hD hU hθ hdθ
  convert square_weak_residual_base P hP f (fun x i=>θ x*U x i)
    (by positivity) (by positivity) hD' hU' using 1
  congr 1
  apply Finset.sum_congr rfl; intro x _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

end SKGapCutoff.Static

end
end

end OAI
