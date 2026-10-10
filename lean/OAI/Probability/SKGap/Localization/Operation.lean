import Mathlib
import OAI.Probability.SKGap.Matrix.DiscreteMatrixCalculus
import OAI.Probability.SKGap.Localization.Error

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

def vectorNorm (u : Fin n→ℝ) : ℝ := ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖

lemma vectorNorm_sq (u : Fin n→ℝ) : vectorNorm u^2=∑i,(u i)^2 := by
  exact EuclideanSpace.real_norm_sq_eq _

lemma vectorNorm_nonneg (u : Fin n→ℝ) : 0 ≤ vectorNorm u := norm_nonneg _

lemma vectorNorm_mul (a s : Fin n→ℝ) {A : ℝ} (hA : 0 ≤ A) (ha : ∀i,|a i| ≤ A) :
    vectorNorm (fun i=>a i*s i) ≤ A*vectorNorm s := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hA (vectorNorm_nonneg _))
  simp only [←sq,vectorNorm_sq,mul_pow]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_right
    (by nlinarith [sq_abs (a i),ha i,abs_nonneg (a i)]) (sq_nonneg _)

lemma row_scaled_frobenius (D : Interaction n) (s : Fin n→ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hD : ∀i,∑k,(D i k)^2 ≤ R^2) :
    ‖Matrix.of (fun i k=>s i*D i k)‖ ≤ R*vectorNorm s := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hR (vectorNorm_nonneg _))
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow,vectorNorm_sq]
  simp only [Matrix.of_apply,mul_pow,←Finset.mul_sum]
  calc
    _  ≤  ∑i,(s i)^2*R^2 := Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (hD i) (sq_nonneg _)
    _ = _ := by rw [←Finset.sum_mul]; ring

lemma row_entry_bound (D : Interaction n) {R : ℝ} (hR : 0 ≤ R)
    (hD : ∀i,∑k,(D i k)^2 ≤ R^2) (i k : Fin n) : |D i k| ≤ R := by
  have H: (D i k)^2 ≤ R^2 :=
    (Finset.single_le_sum (fun l _=>sq_nonneg (D i l)) (Finset.mem_univ k)).trans (hD i)
  nlinarith [sq_abs (D i k),abs_nonneg (D i k)]

lemma multiplier_frobenius (a : Fin n→ℝ) (D : Interaction n) {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀i,|a i| ≤ A) : ‖Matrix.of (fun i k=>a i*D i k)‖ ≤ A*‖D‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hA (norm_nonneg _))
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow,SKGap.frobenius_sq]
  simp only [Matrix.of_apply,mul_pow,Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro k _
  exact mul_le_mul_of_nonneg_right (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (a i)) (ha i) 2) (sq_nonneg _)

lemma product_remainder_frobenius (A D : Interaction n) (x : Spin n) {R : ℝ}
    (hR : 0 ≤ R) (hA : ∀i,∑k,(A i k)^2 ≤ R^2) :
    ‖Matrix.of (fun i k=>2*spin x k*A i k*D i k)‖ ≤ 2*R*‖D‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow,mul_pow,SKGap.frobenius_sq]
  simp only [Matrix.of_apply,mul_pow,spin_sq,mul_one,Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro k _
  have H:=row_entry_bound A hR hA i k
  have HH : (A i k)^2 ≤ R^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (A i k)) H 2
  nlinarith [mul_nonneg (sq_nonneg (D i k)) (sub_nonneg.mpr HH)]

lemma source_derivative_product (a s : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>a x i*s x i) x=
      (fun i k=>a x i*derivativeMatrix s x i k)+
      (fun i k=>s x i*derivativeMatrix a x i k)-
      (fun i k=>2*spin x k*derivativeMatrix a x i k*derivativeMatrix s x i k) := by
  ext i k
  exact halfDiff_mul k (fun x=>a x i) (fun x=>s x i) x

lemma source_frobenius (a s : VectorFields n) (x : Spin n) {A R : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R) (ha : ∀i,|a x i| ≤ A)
    (hda : ∀i,∑k,(derivativeMatrix a x i k)^2 ≤ R^2) :
    ‖derivativeMatrix (fun x i=>a x i*s x i) x‖ ≤
      A*‖derivativeMatrix s x‖+R*vectorNorm (s x)+2*R*‖derivativeMatrix s x‖ := by
  rw [source_derivative_product]
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (multiplier_frobenius _ _ hA ha)
      (row_scaled_frobenius _ _ hR hda))) (product_remainder_frobenius _ _ x hR hda))

lemma source_sum_frobenius {ι : Type*} [Fintype ι] (a s : ι→VectorFields n) (x : Spin n)
    (A R : ι→ℝ) (hA : ∀l,0 ≤ A l) (hR : ∀l,0 ≤ R l) (ha : ∀l i,|a l x i| ≤ A l)
    (hda : ∀l i,∑k,(derivativeMatrix (a l) x i k)^2 ≤ (R l)^2) :
    ‖derivativeMatrix (fun x i=>∑l,a l x i*s l x i) x‖ ≤
      ∑l,(A l*‖derivativeMatrix (s l) x‖+R l*vectorNorm (s l x)+2*R l*‖derivativeMatrix (s l) x‖) := by
  have he : derivativeMatrix (fun x i=>∑l,a l x i*s l x i) x=
      ∑l,derivativeMatrix (fun x i=>a l x i*s l x i) x := by
    ext i k
    simp only [Matrix.sum_apply,derivativeMatrix,halfDiff_sum]
  rw [he]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _=>source_frobenius _ _ x (hA l) (hR l) (ha l) (hda l))

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_add (u v : Fin n→ℝ) :
    vectorNorm (u+v) ≤ vectorNorm u+vectorNorm v := by
  exact norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v)

lemma vectorNorm_smul (c : ℝ) (u : Fin n→ℝ) :
    vectorNorm (c • u)=|c| *vectorNorm u := by
  exact norm_smul c (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))

lemma vectorNorm_sum {ι : Type*} [Fintype ι] (u : ι→Fin n→ℝ) :
    vectorNorm (∑l,u l) ≤ ∑l,vectorNorm (u l) := by
  change ‖(WithLp.toLp 2 (∑l,u l) : EuclideanSpace ℝ (Fin n))‖≤_
  have he : (WithLp.toLp 2 (∑l,u l) : EuclideanSpace ℝ (Fin n))=∑l,WithLp.toLp 2 (u l) := by
    ext i; simp [Finset.sum_apply]
  rw [he]
  exact norm_sum_le _ _

lemma vectorNorm_mono {u v : Fin n→ℝ} (h : ∀i,|u i|≤|v i|) : vectorNorm u ≤ vectorNorm v := by
  apply nonneg_le_nonneg_of_sq_le_sq (vectorNorm_nonneg _)
  simp only [←sq,vectorNorm_sq]
  exact Finset.sum_le_sum fun i _=>by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u i)) (h i) 2

lemma vectorNorm_abs (u : Fin n→ℝ) : vectorNorm (fun i=>|u i|)=vectorNorm u := by
  apply (sq_eq_sq₀ (vectorNorm_nonneg _) (vectorNorm_nonneg _)).mp
  simp [vectorNorm_sq]

lemma vectorNorm_matrix_mul (J : Interaction n) (u : Fin n→ℝ) :
    vectorNorm (J.mulVec u) ≤ SKGap.opNorm J*vectorNorm u := by
  exact (Matrix.toEuclideanCLM (𝕜:=ℝ) J).le_opNorm (WithLp.toLp 2 u)

lemma siteMean_square (U : VectorFields n) (x : Spin n) (hn : 0<n) :
    (n:ℝ)*(siteMean U x)^2 ≤ (vectorNorm (U x))^2 := by
  have H:=sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=U x)
  simp only [Finset.card_univ,Fintype.card_fin] at H
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  dsimp only [siteMean]
  rw [div_pow,vectorNorm_sq]
  apply (mul_le_mul_iff_left₀ hnR).mp
  field_simp
  nlinarith

lemma primary_mean_size (U m : VectorFields n) (x : Spin n) (hn : 0<n)
    (hm : ∀i,|m x i|≤1) :
    vectorNorm (fun i=>siteMean U x*m x i) ≤ vectorNorm (U x) := by
  apply nonneg_le_nonneg_of_sq_le_sq (vectorNorm_nonneg _)
  simp only [←sq,vectorNorm_sq,mul_pow]
  calc
    _ ≤ ∑_i:Fin n,(siteMean U x)^2 := by
      apply Finset.sum_le_sum; intro i _
      have H : (m x i)^2≤1 := by
        simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg (m x i)) (hm i) 2
      nlinarith [sq_nonneg (siteMean U x)]
    _ = (n:ℝ)*(siteMean U x)^2 := by simp
    _ ≤ _ := by simpa only [vectorNorm_sq] using siteMean_square U x hn

lemma scaled_frobenius_by_rows (D : Interaction n) (a : ℝ) {C P : ℝ}
    (hC : 0≤C) (hP : 0≤P) (ha : (n:ℝ)*a^2≤C^2)
    (hD : ∀i,∑k,(D i k)^2≤P^2) : ‖a • D‖≤C*P := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC hP)
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow]
  simp only [Matrix.smul_apply,smul_eq_mul,mul_pow]
  calc
    _ ≤ ∑_i:Fin n,a^2*P^2 := Finset.sum_le_sum fun i _=>by
      rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hD i) (sq_nonneg _)
    _ = ((n:ℝ)*a^2)*P^2 := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ha (sq_nonneg _)

lemma primary_mean_frobenius (U m : VectorFields n) (x : Spin n) (hn : 0<n) {C P : ℝ}
    (hC : 0≤C) (hP : 0≤P) (hu : vectorNorm (U x)≤C) (hdu : ‖derivativeMatrix U x‖≤C)
    (hm : ∀i,|m x i|≤1) (hdm : SKGap.opNorm (derivativeMatrix m x)≤P) :
    ‖derivativeMatrix (fun y i=>siteMean U y*m y i) x‖≤C*(1+3*P) := by
  have hav : (n:ℝ)*(siteMean U x)^2≤C^2 := (siteMean_square U x hn).trans
    (pow_le_pow_left₀ (vectorNorm_nonneg _) hu 2)
  have hdav : (n:ℝ)*‖derivativeVector (siteMean U) x‖^2≤C^2 :=
    siteMean_derivative_square_bound hn ((opNorm_le_frobenius _).trans hdu)
  have hs := scaled_frobenius_by_rows (derivativeMatrix m x) (siteMean U x) hC hP hav (fun i=>
    (SKGap.SourceError.matrix_row_square_le _ i).trans (pow_le_pow_left₀ (norm_nonneg _) hdm 2))
  have he := product_derivative_error hn hC hdm hm hdav
  calc
    _ ≤ ‖derivativeMatrix (fun y i=>siteMean U y*m y i) x-siteMean U x • derivativeMatrix m x‖+
      ‖siteMean U x • derivativeMatrix m x‖ := norm_le_norm_sub_add _ _
    _ ≤ (C+2*P*C)+C*P := add_le_add he hs
    _ = _ := by ring

lemma coefficient_mean_value (a : VectorFields n) (x : Spin n) {A : ℝ}
    (hA : 0≤A) (ha : ∀i,|a x i|≤A) : |siteMean a x|≤A := by
  by_cases hn : n=0
  · subst n; simp [siteMean,hA]
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [siteMean,abs_div,abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑i,|a x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_i:Fin n,A := Finset.sum_le_sum fun i _=>ha i
    _ = _ := by simp [mul_comm]

lemma coefficient_mean_difference (a : VectorFields n) (x : Spin n) {R : ℝ}
    (hR : 0≤R) (hda : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2) :
    ‖derivativeVector (siteMean a) x‖≤R := by
  have he : derivativeVector (siteMean a) x = (n:ℝ)⁻¹ •
      ∑i,WithLp.toLp 2 (fun k=>derivativeMatrix a x i k) := by
    ext k
    simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_toLp]
    simp only [halfDiff,siteMean,derivativeMatrix]
    rw [←Finset.sum_div,Finset.sum_sub_distrib]
    ring
  rw [he,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (Nat.cast_nonneg n)]
  by_cases hn : n=0
  · subst n; simp [hR]
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  calc
    _ ≤ (n:ℝ)⁻¹*(∑_i:Fin n,R) := mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>by
        apply nonneg_le_nonneg_of_sq_le_sq hR
        simpa only [←sq,EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp] using hda i)) (inv_nonneg.mpr hnR.le)
    _ = R := by simp [hnR.ne']

end SKGapCutoff.Recipe

end
end

end OAI
