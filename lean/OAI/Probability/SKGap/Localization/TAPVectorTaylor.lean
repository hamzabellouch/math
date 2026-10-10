import Mathlib
import OAI.Probability.SKGap.Localization.TAPScalarTaylor
import OAI.Probability.SKGap.Entropy.WeightedMomentComparison

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators

def varianceAverage {n : ℕ} (y : Field n) : ℝ := 1-overlap y

def varianceLinear {n : ℕ} (y d : Field n) : ℝ :=
  (-2/(n:ℝ))*∑ i,magnetization y i*spinVariance y i*d i

def magnetizationRemainder {n : ℕ} (y d : Field n) : Field n :=
  magnetization (y+d)-magnetization y-(fun i => spinVariance y i*d i)

lemma varianceAverage_eq_average {n : ℕ} (hn : 0 < n) (y : Field n) :
    varianceAverage y=(∑ i,spinVariance y i)/(n:ℝ) := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  dsimp [varianceAverage,overlap,spinVariance]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  field_simp

lemma varianceAverage_bounds {n : ℕ} (hn : 0 < n) (y : Field n) :
    0 ≤ varianceAverage y ∧ varianceAverage y ≤ 1 := by
  dsimp [varianceAverage]
  exact ⟨sub_nonneg.mpr (overlap_lt_one hn y).le,sub_le_self _ (overlap_nonneg y)⟩

lemma magnetization_norm_bound {n : ℕ} (y : Field n) :
    vectorNorm (magnetization y) ≤ sqrt (n:ℝ) := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) (sqrt_nonneg _)).mp
  rw [vectorNorm_sq,Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ ∑ _i : Fin n,(1:ℝ) := Finset.sum_le_sum (fun i _ => (tanh_sq_lt_one (y i)).le)
    _ = _ := by simp

lemma vectorNorm_le_of_sq_sum {n : ℕ} {v : Field n} {c : ℝ} (hc : 0 ≤ c)
    (hb : ∑ i,v i^2 ≤ c^2) : vectorNorm v ≤ c := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) hc).mp
  exact (vectorNorm_sq v).trans_le hb

lemma magnetization_difference_norm {n : ℕ} (y d : Field n) :
    vectorNorm (magnetization (y+d)-magnetization y) ≤ vectorNorm d := by
  apply vectorNorm_le_of_sq_sum (vectorNorm_nonneg _)
  rw [vectorNorm_sq]
  apply Finset.sum_le_sum
  intro i _
  have hh := tanh_lipschitz_abs (y i+d i) (y i)
  rw [add_sub_cancel_left] at hh
  simpa only [Pi.sub_apply,Pi.add_apply,magnetization,sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hh |>.trans_eq (sq_abs (d i))

lemma magnetization_remainder_norm {n : ℕ} (y d : Field n) :
    vectorNorm (magnetizationRemainder y d) ≤ 2*sqrt (∑ i,d i^4) := by
  apply vectorNorm_le_of_sq_sum (by positivity)
  rw [mul_pow,Real.sq_sqrt (Finset.sum_nonneg (fun i _ => (by positivity : 0 ≤ d i^4))),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh := tanh_scalar_remainder (y i) (d i)
  have hh' := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hh
  simpa only [magnetizationRemainder,Pi.sub_apply,Pi.add_apply,magnetization,spinVariance,
    sq_abs,mul_pow,← pow_mul] using hh'

lemma varianceAverage_remainder {n : ℕ} (hn : 0 < n) (y d : Field n) :
    |varianceAverage (y+d)-varianceAverage y-varianceLinear y d| ≤
      6/(n:ℝ)*vectorNorm d^2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [varianceAverage_eq_average hn,varianceAverage_eq_average hn,vectorNorm_sq]
  have he : (∑ i,spinVariance (y+d) i)/(n:ℝ)-
      (∑ i,spinVariance y i)/(n:ℝ)-varianceLinear y d=
      (∑ i,(spinVariance (y+d) i-spinVariance y i-
        (-2*magnetization y i*spinVariance y i)*d i))/(n:ℝ) := by
    have hlin : (∑ i,(-2*magnetization y i*spinVariance y i)*d i)=
        -2*∑ i,magnetization y i*spinVariance y i*d i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; ring
    simp only [varianceLinear,Finset.sum_sub_distrib,hlin]
    field_simp
  rw [he,abs_div,abs_of_pos hn0]
  apply (div_le_iff₀ hn0).mpr
  calc
    _ ≤ ∑ i,|(spinVariance (y+d) i-spinVariance y i-(-2*magnetization y i*spinVariance y i)*d i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,6*d i^2 := Finset.sum_le_sum (fun i _ => scalar_variance_remainder (y i) (d i))
    _ = _ := by simp only [vectorSqNorm,← Finset.mul_sum]; field_simp

lemma varianceAverage_difference {n : ℕ} (hn : 0 < n) (y d : Field n) :
    |varianceAverage (y+d)-varianceAverage y| ≤ 2/sqrt (n:ℝ)*vectorNorm d := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hs0 : sqrt (n:ℝ) ≠ 0 := ne_of_gt (sqrt_pos.mpr hn0)
  rw [varianceAverage_eq_average hn,varianceAverage_eq_average hn,← sub_div,
    ← Finset.sum_sub_distrib,abs_div,abs_of_pos hn0]
  apply (div_le_iff₀ hn0).mpr
  calc
    _ ≤ ∑ i,|spinVariance (y+d) i-spinVariance y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,2*|d i| := Finset.sum_le_sum (fun i _ => by
      simpa only [spinVariance,magnetization,Pi.add_apply,add_sub_cancel_left] using scalar_variance_lipschitz_abs (y i+d i) (y i))
    _ = 2*∑ i,|d i| := by rw [Finset.mul_sum]
    _ ≤ 2*(sqrt (n:ℝ)*vectorNorm d) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hh := sum_abs_le_sqrt_card_l2 d
      have he : sqrt (∑ i,d i^2)=vectorNorm d := by
        change sqrt (vectorSqNorm d)=vectorNorm d
        rw [← vectorNorm_sq,Real.sqrt_sq (vectorNorm_nonneg _)]
      simpa only [Fintype.card_fin,he] using hh
    _ = _ := by field_simp; rw [Real.sq_sqrt hn0.le]; ring

lemma tap_remainder_identity {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y d : Field n) :
    tapField j J h (y+d)-tapField j J h y-(fieldJacobian j J y)*ᵥd=
      (j*varianceAverage y) • magnetizationRemainder y d+
      (j*(varianceAverage (y+d)-varianceAverage y-varianceLinear y d)) • magnetization y+
      (j*(varianceAverage (y+d)-varianceAverage y)) • (magnetization (y+d)-magnetization y)-
      J*ᵥmagnetizationRemainder y d := by
  have hjac (i : Fin n) : (fieldJacobian j J y*ᵥd) i=
      d i+onsager j y*(spinVariance y i*d i)-
      (∑ k,J i k*(spinVariance y k*d k))+j*varianceLinear y d*magnetization y i := by
    change (∑ k,fieldJacobian j J y i k*d k)=_
    have he : (∑ k,fieldJacobian j J y i k*d k)=
        (∑ k,(if i=k then 1 else (0:ℝ))*d k)+
        onsager j y*(∑ k,(if i=k then 1 else (0:ℝ))*spinVariance y k*d k)-
        (∑ k,J i k*(spinVariance y k*d k))-
        (2*j/(n:ℝ))*magnetization y i*(∑ k,magnetization y k*spinVariance y k*d k) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [fieldJacobian,hessianCore]
      ring
    rw [he]
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    dsimp [varianceLinear]
    ring
  ext i
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [hjac]
  simp only [tapField,Pi.add_apply,onsager,varianceAverage,magnetizationRemainder,Pi.sub_apply,
    Matrix.mulVec,dotProduct,mul_sub,Finset.sum_sub_distrib]
  ring

attribute [local irreducible] vectorNorm varianceAverage varianceLinear magnetizationRemainder tapField fieldJacobian magnetization

theorem tap_remainder_norm {n : ℕ} (hn : 0 < n) {j K : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y d : Field n) :
    vectorNorm (tapField j J h (y+d)-tapField j J h y-(fieldJacobian j J y)*ᵥd) ≤
      2*(j+K)*sqrt (∑ i,d i^4)+(8*j/sqrt (n:ℝ))*vectorNorm d^2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hsn : sqrt (n:ℝ) ≠ 0 := ne_of_gt (sqrt_pos.mpr hn0)
  have hnd := vectorNorm_nonneg d
  let rm := magnetizationRemainder y d
  let rb := varianceAverage (y+d)-varianceAverage y-varianceLinear y d
  let db := varianceAverage (y+d)-varianceAverage y
  have hb := varianceAverage_bounds hn y
  have h₁ : vectorNorm ((j*varianceAverage y) • rm) ≤ j*vectorNorm rm := by
    change vectorNorm (fun i => (j*varianceAverage y)*rm i) ≤ _
    rw [vectorNorm_smul,abs_of_nonneg (mul_nonneg hj hb.1)]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hb.2]) (vectorNorm_nonneg _)
  have h₂ : vectorNorm ((j*rb) • magnetization y) ≤
      (6*j/sqrt (n:ℝ))*vectorNorm d^2 := by
    change vectorNorm (fun i => (j*rb)*magnetization y i) ≤ _
    rw [vectorNorm_smul,abs_mul,abs_of_nonneg hj]
    calc
      _ ≤ (j*(6/(n:ℝ)*vectorNorm d^2))*sqrt (n:ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (varianceAverage_remainder hn y d) hj)
          (magnetization_norm_bound y) (vectorNorm_nonneg _) (by positivity)
      _ = _ := by field_simp; rw [Real.sq_sqrt hn0.le]; ring
  have h₃ : vectorNorm ((j*db) • (magnetization (y+d)-magnetization y)) ≤
      (2*j/sqrt (n:ℝ))*vectorNorm d^2 := by
    change vectorNorm (fun i => (j*db)*(magnetization (y+d)-magnetization y) i) ≤ _
    rw [vectorNorm_smul,abs_mul,abs_of_nonneg hj]
    calc
      _ ≤ (j*(2/sqrt (n:ℝ)*vectorNorm d))*vectorNorm d :=
        mul_le_mul (mul_le_mul_of_nonneg_left (varianceAverage_difference hn y d) hj)
          (magnetization_difference_norm y d) (vectorNorm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [tap_remainder_identity]
  calc
    _ ≤ (vectorNorm ((j*varianceAverage y) • rm)+vectorNorm ((j*rb) • magnetization y)+
      vectorNorm ((j*db) • (magnetization (y+d)-magnetization y)))+vectorNorm (J*ᵥrm) := by
        exact (vectorNorm_sub_le _ _).trans
          (add_le_add ((vectorNorm_add_le _ _).trans
            (add_le_add (vectorNorm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (j*vectorNorm rm+(6*j/sqrt (n:ℝ))*vectorNorm d^2+
      (2*j/sqrt (n:ℝ))*vectorNorm d^2)+K*vectorNorm rm :=
        add_le_add (add_le_add (add_le_add h₁ h₂) h₃) (hJ rm)
    _ = (j+K)*vectorNorm rm+(8*j/sqrt (n:ℝ))*vectorNorm d^2 := by ring
    _ ≤ (j+K)*(2*sqrt (∑ i,d i^4))+(8*j/sqrt (n:ℝ))*vectorNorm d^2 :=
      add_le_add (mul_le_mul_of_nonneg_left (magnetization_remainder_norm y d) (add_nonneg hj hK)) le_rfl
    _ = _ := by ring

end SKGap
end
end

end OAI
