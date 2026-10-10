import Mathlib
import OAI.Probability.SKGap.Matrix.LogDetUniform
import OAI.Probability.SKGap.Stability.FieldIntegralReduction

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

theorem field_logdet_uniform {j ε : ℝ} (hj : 0 < j) (hj1 : j < 1) (hε : 0 < ε) :
    ∃ γ : ℝ,0 < γ ∧ ∃ N : ℕ,0 < N ∧ ∀ n : ℕ,N ≤ n →
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ∃ y : Field n,(n:ℝ)*(j*varianceAverage y^2+ε) <
        log ((fieldJacobian j (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) y)ᵀ*
          fieldJacobian j (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) y+γ • 1).det} ≤
      4*exp (-min 1 (1/(π^2*j))*(n:ℝ)) := by
  obtain ⟨γ,hγ,hγbound⟩ := actual_simultaneous_logdet hj hj1 hε
  obtain ⟨N,hN,hbound⟩ := hγbound γ hγ le_rfl 2 (3*j)
  refine ⟨γ,hγ,N,hN,?_⟩
  intro n hn
  have hn0 : 0 < n := hN.trans_le hn
  have hnreal : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  apply (measureReal_mono (s₂ := {g | ∃ a : Fin n → ℝ,(∀ i,0 ≤ a i) ∧ (∀ i,a i ≤ 1) ∧
    ∃ E : Matrix (Fin n) (Fin n) ℝ,E.rank ≤ 2 ∧ opNorm E ≤ 3*j ∧
      j*(coordAverage a)^2+ε < LogDet.regularizedLogDet γ
        (1+((j*coordAverage a) • 1-goeMatrix (j/(n:ℝ)) g)*diagonal a+E)}) ?_
    (measure_ne_top _ _)).trans (hbound n hn)
  rintro g ⟨y,hy⟩
  refine ⟨spinVariance y,fun i=>(spinVariance_pos y i).le,spinVariance_le_one y,
    plantedJacobianPerturbation j y,plantedJacobianPerturbation_rank j y,
    plantedJacobianPerturbation_norm hn0 hj.le y,?_⟩
  rw [← fieldJacobian_planted_formula hn0]
  have hav : coordAverage (spinVariance y)=varianceAverage y := by
    simpa only [coordAverage,Fintype.card_fin] using (varianceAverage_eq_average hn0 y).symm
  rw [hav]
  simpa only [LogDet.regularizedLogDet,LogDet.regularizedGram,Fintype.card_fin,lt_div_iff₀ hnreal,mul_comm] using hy
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators

lemma spinVariance_difference_norm {n : ℕ} (y d : Field n) :
    vectorNorm (spinVariance (y+d)-spinVariance y) ≤ 2*vectorNorm d := by
  apply vectorNorm_le_of_sq_sum (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (vectorNorm_nonneg _))
  rw [mul_pow,vectorNorm_sq,vectorSqNorm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh : |spinVariance (y+d) i-spinVariance y i| ≤ 2*|d i| := by
    simpa only [spinVariance,magnetization,Pi.add_apply,add_sub_cancel_left] using
      scalar_variance_lipschitz_abs (y i+d i) (y i)
  have ha := mul_self_le_mul_self (abs_nonneg _) hh
  simpa only [sq_abs,← pow_two,mul_pow,Pi.sub_apply] using ha

lemma dot_magnetization_sq_difference {n : ℕ} (y d v : Field n) :
    |((∑ i,magnetization (y+d) i*v i)^2)-(∑ i,magnetization y i*v i)^2| ≤
      2*sqrt (n:ℝ)*vectorNorm d*vectorSqNorm v := by
  let a := ∑ i,magnetization (y+d) i*v i
  let b := ∑ i,magnetization y i*v i
  have ha : |a| ≤ sqrt (n:ℝ)*vectorNorm v :=
    (vector_dot_abs_le (magnetization (y+d)) v).trans
      (mul_le_mul_of_nonneg_right (magnetization_norm_bound (y+d)) (vectorNorm_nonneg _))
  have hb : |b| ≤ sqrt (n:ℝ)*vectorNorm v :=
    (vector_dot_abs_le (magnetization y) v).trans
      (mul_le_mul_of_nonneg_right (magnetization_norm_bound y) (vectorNorm_nonneg _))
  have hab : |a-b| ≤ vectorNorm d*vectorNorm v := by
    have he : a-b=∑ i,(magnetization (y+d)-magnetization y) i*v i := by
      simp only [a,b,Pi.sub_apply,sub_mul,Finset.sum_sub_distrib]
    rw [he]
    exact (vector_dot_abs_le _ _).trans
      (mul_le_mul_of_nonneg_right (magnetization_difference_norm y d) (vectorNorm_nonneg _))
  have hsum : |a+b| ≤ 2*sqrt (n:ℝ)*vectorNorm v := (abs_add_le _ _).trans (by linarith)
  change |a^2-b^2| ≤ _
  rw [sq_sub_sq,abs_mul]
  apply (mul_le_mul hsum hab (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sqrt_nonneg _)) (vectorNorm_nonneg _))).trans_eq
  rw [← vectorNorm_sq]
  ring

lemma hessian_field_difference {n : ℕ} (hn : 0 < n) {j A : ℝ} (hj : 0 ≤ j) (_hA : 0 ≤ A)
    (J : Matrix (Fin n) (Fin n) ℝ) (y d a x : Field n)
    (ha0 : ∀ i,0 ≤ a i) (haA : ∀ i,a i ≤ A) :
    |quadraticForm (fieldHessian j J (y+d) a) x-quadraticForm (fieldHessian j J y a) x| ≤
      (6*j*A/sqrt (n:ℝ))*vectorNorm d*vectorSqNorm x := by
  let v : Field n := fun i=>sqrt (a i)*x i
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hs0 : 0 < sqrt (n:ℝ) := sqrt_pos.mpr hn0
  have hv : vectorSqNorm v ≤ A*vectorSqNorm x := by
    unfold vectorSqNorm v
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _=>by
      rw [mul_pow,sq_sqrt (ha0 i)]
      exact mul_le_mul_of_nonneg_right (haA i) (sq_nonneg _))
  have hb : |onsager j (y+d)-onsager j y| ≤ j*(2/sqrt (n:ℝ)*vectorNorm d) := by
    unfold onsager
    rw [← mul_sub,abs_mul,abs_of_nonneg hj]
    exact mul_le_mul_of_nonneg_left (varianceAverage_difference hn y d) hj
  have he : quadraticForm (fieldHessian j J (y+d) a) x-quadraticForm (fieldHessian j J y a) x=
      (onsager j (y+d)-onsager j y)*vectorSqNorm v-
      (2*j/(n:ℝ))*((∑ i,magnetization (y+d) i*v i)^2-(∑ i,magnetization y i*v i)^2) := by
    rw [hessian_quadratic_formula,hessian_quadratic_formula]
    dsimp [v]
    ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg (vectorSqNorm_nonneg v),abs_mul,
    abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hj) hn0.le)]
  have hq := dot_magnetization_sq_difference y d v
  have hfirst := mul_le_mul_of_nonneg_right hb (vectorSqNorm_nonneg v)
  have hsecond := mul_le_mul_of_nonneg_left hq (div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hj) hn0.le)
  have hfactor : j*(2/sqrt (n:ℝ)*vectorNorm d)*vectorSqNorm v+
      (2*j/(n:ℝ))*(2*sqrt (n:ℝ)*vectorNorm d*vectorSqNorm v)=
      (6*j/sqrt (n:ℝ))*vectorNorm d*vectorSqNorm v := by
    field_simp
    rw [sq_sqrt hn0.le]
    ring
  apply (add_le_add hfirst hsecond).trans
  rw [hfactor]
  calc
    _ ≤ (6*j/sqrt (n:ℝ))*vectorNorm d*(A*vectorSqNorm x) :=
      mul_le_mul_of_nonneg_left hv (mul_nonneg (by positivity) (vectorNorm_nonneg _))
    _ = _ := by ring

lemma badField_neighborhood {n : ℕ} (hn : 0 < n) {j A ε c r : ℝ}
    (hj : 0 ≤ j) (hA : 0 ≤ A) (hε : 0 < ε) (_hr0 : 0 ≤ r)
    (hrε : 2*r ≤ ε/2) (hrc : 6*j*A*r ≤ c/2)
    (W : Matrix (Fin n) (Fin n) ℝ) (y d : Field n)
    (hy : (W,y)∈badFieldSet n j A (ε/2) (c/2))
    (hd : vectorNorm d ≤ r*sqrt (n:ℝ)) :
    (W,y+d)∈badFieldSet n j A ε c := by
  obtain ⟨a,ha,hclose,x,hx,hquad⟩ := hy
  have hs := sqrt_nonneg (n:ℝ)
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hnorm : vectorNorm (a-spinVariance y) ≤ (ε/2)*sqrt (n:ℝ) := by
    apply vectorNorm_le_of_sq_sum (by positivity)
    simpa only [Pi.sub_apply,mul_pow,sq_sqrt hn0.le] using hclose
  have hdist : vectorNorm (a-spinVariance (y+d)) ≤ ε*sqrt (n:ℝ) := by
    have he : a-spinVariance (y+d)=(a-spinVariance y)-(spinVariance (y+d)-spinVariance y) := by abel
    rw [he]
    apply (vectorNorm_sub_le _ _).trans
    have hm := (spinVariance_difference_norm y d).trans (mul_le_mul_of_nonneg_left hd (by norm_num))
    nlinarith [mul_le_mul_of_nonneg_right hrε hs]
  refine ⟨a,ha,?_,x,hx,?_⟩
  · have hh := mul_self_le_mul_self (vectorNorm_nonneg (a-spinVariance (y+d))) hdist
    simpa only [← pow_two,vectorNorm_sq,vectorSqNorm,Pi.sub_apply,mul_pow,sq_sqrt hn0.le] using hh
  · have hv : vectorSqNorm x.ofLp=1 := by
      rw [← vectorNorm_sq]
      change ‖WithLp.toLp 2 x.ofLp‖^2=1
      simp only [WithLp.toLp_ofLp,hx,one_pow]
    have hb := hessian_field_difference hn hj hA (plantedInteraction j W) y d a x.ofLp
      (fun i=>(ha i).1) (fun i=>(ha i).2)
    rw [hv,mul_one] at hb
    have hc := (mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 6*j*A/sqrt (n:ℝ)))
    have he : (6*j*A/sqrt (n:ℝ))*(r*sqrt (n:ℝ))=6*j*A*r := by field_simp
    rw [he] at hc
    linarith [le_abs_self (quadraticForm (fieldHessian j (plantedInteraction j W) (y+d) a) x.ofLp-
      quadraticForm (fieldHessian j (plantedInteraction j W) y a) x.ofLp)]
end SKGap
end
end

end OAI
