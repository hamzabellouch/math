import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkTangentError

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma bulkCovariance_bound (N : ℕ) (v : ℕ→ℝ) {C r : ℝ}
    (hC : 0≤C) (hv : ∀ j, |v (j+1)|≤C) (hr : |r|≤1) :
    |bulkCovariance N v r|≤C^2 := by
  have ht (j : Fin N) :
      |((2:ℝ)^(-((j.val+1:ℕ):ℤ)))^2*v (j.val+1)^2*r^(j.val+1)|≤C^2*(1/2:ℝ)^(j.val+1) := by
    rw [perturbationWeight_eq,abs_mul,abs_mul,abs_sq,abs_sq,abs_pow]
    have hw0 : 0≤(1/2:ℝ)^(j.val+1) := by positivity
    have hw1 : (1/2:ℝ)^(j.val+1)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hv2 : v (j.val+1)^2≤C^2 := by
      exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hC] using hv j.val)
    calc
      _ ≤ ((1/2:ℝ)^(j.val+1))^2*C^2*1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hv2 (sq_nonneg _))
          (pow_le_one₀ (abs_nonneg r) hr) (by positivity) (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (show ((1/2:ℝ)^(j.val+1))^2≤(1/2:ℝ)^(j.val+1) by nlinarith) (sq_nonneg C)]
  unfold bulkCovariance
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j : Fin N,C^2*(1/2:ℝ)^(j.val+1) := Finset.sum_le_sum fun j _=>ht j
    _ = C^2*(∑ j : Fin N,(1/2:ℝ)^(j.val+1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ C^2*1 := mul_le_mul_of_nonneg_left (half_power_sum_le_one N) (sq_nonneg C)
    _ = _ := mul_one _

lemma bulkCovariance_scaled_hasDerivAt (N : ℕ) (v : ℕ→ℝ) (r : ℝ) :
    HasDerivAt (fun t=>bulkScale N^2*bulkCovariance N v t)
      (bulkCovarianceDerivative N v r) r := by
  have he (t : ℝ) : bulkScale N^2*bulkCovariance N v t=
      ∑ j : Fin N,bulkAmplitude N v j^2*t^(j.val+1) := by
    simp only [bulkCovariance,bulkAmplitude,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  simpa [bulkCovarianceDerivative,mul_assoc] using HasDerivAt.fun_sum
    (u:=Finset.univ) (fun j (_ : j∈(Finset.univ : Finset (Fin N)))=>
      ((hasDerivAt_id r).pow (j.val+1)).const_mul (bulkAmplitude N v j^2))

lemma bulkCovariance_scaled_lipschitz (N : ℕ) (v : ℕ→ℝ) {C r s : ℝ}
    (hC : 0≤C) (hv : ∀ j, |v (j+1)|≤C) (hr : |r|≤1) (hs : |s|≤1) :
    |bulkScale N^2*bulkCovariance N v s-bulkScale N^2*bulkCovariance N v r|≤
      C^2*bulkScale N^2*|s-r| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t∈Icc (-1:ℝ) 1)=>(bulkCovariance_scaled_hasDerivAt N v t).hasDerivWithinAt)
    (fun t ht=>show ‖bulkCovarianceDerivative N v t‖≤C^2*bulkScale N^2 by
      simpa only [Real.norm_eq_abs] using bulkCovarianceDerivative_bound N v hC hv (abs_le.mpr ht))
    (convex_Icc (-1:ℝ) 1) (abs_le.mp hr) (abs_le.mp hs)
  simpa only [Real.norm_eq_abs] using hh

lemma bulkCovariance_dimension_tail (N L : ℕ) (v : ℕ→ℝ) {C r : ℝ}
    (hC : 0≤C) (hv : ∀ j, |v (j+1)|≤C) (hr : |r|≤1) :
    |bulkCovariance (N+L) v r-bulkCovariance N v r|≤
      (L:ℝ)*C^2*(1/2:ℝ)^(N+1) := by
  have he : bulkCovariance (N+L) v r-bulkCovariance N v r=
      ∑ j : Fin L,((2:ℝ)^(-((N+j.val+1:ℕ):ℤ)))^2*v (N+j.val+1)^2*r^(N+j.val+1) := by
    unfold bulkCovariance
    rw [Fin.sum_univ_add]
    simp only [Fin.val_castAdd,Fin.val_natAdd,add_sub_cancel_left]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _ : Fin L,C^2*(1/2:ℝ)^(N+1) := by
      apply Finset.sum_le_sum
      intro j _
      rw [perturbationWeight_eq,abs_mul,abs_mul,abs_sq,abs_sq,abs_pow]
      have hw0 : 0≤(1/2:ℝ)^(N+j.val+1) := by positivity
      have hw1 : (1/2:ℝ)^(N+j.val+1)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hwt : (1/2:ℝ)^(N+j.val+1)≤(1/2:ℝ)^(N+1) := by
        have he : N+j.val+1=(N+1)+j.val := by omega
        rw [he,pow_add]
        exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num) : (1/2:ℝ)^j.val≤1) (by positivity)).trans_eq (mul_one _)
      have hv2 : v (N+j.val+1)^2≤C^2 := by
        exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hC] using hv (N+j.val))
      calc
        _ ≤ ((1/2:ℝ)^(N+j.val+1))^2*C^2*1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hv2 (sq_nonneg _))
            (pow_le_one₀ (abs_nonneg r) hr) (by positivity) (by positivity)
        _ ≤ C^2*(1/2:ℝ)^(N+j.val+1) := by
          nlinarith [mul_le_mul_of_nonneg_left (show ((1/2:ℝ)^(N+j.val+1))^2≤(1/2:ℝ)^(N+j.val+1) by nlinarith) (sq_nonneg C)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hwt (sq_nonneg C)
    _ = _ := by simp; ring

theorem cavity_bulk_covariance_bound (N L : ℕ) (v : ℕ→ℝ) {C r s : ℝ}
    (hC : 0≤C) (hv : ∀ j, |v (j+1)|≤C) (hr : |r|≤1) (hs : |s|≤1) :
    |bulkScale (N+L)^2*bulkCovariance (N+L) v s-bulkScale N^2*bulkCovariance N v r|≤
      C^2*bulkScale (N+L)^2*|s-r|+
        bulkScale (N+L)^2*((L:ℝ)*C^2*(1/2:ℝ)^(N+1))+
        |bulkScale (N+L)^2-bulkScale N^2| * C^2 := by
  calc
    _ ≤ |bulkScale (N+L)^2*bulkCovariance (N+L) v s-bulkScale (N+L)^2*bulkCovariance (N+L) v r|+
        |bulkScale (N+L)^2*bulkCovariance (N+L) v r-bulkScale N^2*bulkCovariance N v r| := abs_sub_le _ _ _
    _ ≤ C^2*bulkScale (N+L)^2*|s-r|+
        (bulkScale (N+L)^2*((L:ℝ)*C^2*(1/2:ℝ)^(N+1))+|bulkScale (N+L)^2-bulkScale N^2| * C^2) := by
      apply add_le_add (bulkCovariance_scaled_lipschitz (N+L) v hC hv hr hs)
      calc
        _ ≤ |bulkScale (N+L)^2*(bulkCovariance (N+L) v r-bulkCovariance N v r)|+
            |(bulkScale (N+L)^2-bulkScale N^2)*bulkCovariance N v r| := by
          convert abs_add_le (bulkScale (N+L)^2*(bulkCovariance (N+L) v r-bulkCovariance N v r))
            ((bulkScale (N+L)^2-bulkScale N^2)*bulkCovariance N v r) using 1
          congr 1
          ring
        _ ≤ _ := by
          rw [abs_mul,abs_sq,abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (bulkCovariance_dimension_tail N L v hC hv hr) (sq_nonneg _))
            (mul_le_mul_of_nonneg_left (bulkCovariance_bound N v hC hv hr) (abs_nonneg _))
    _ = _ := by ring

lemma bulkScale_sq_eq_rpow (N : ℕ) : bulkScale N^2=(N:ℝ)^((3:ℝ)/4) := by
  unfold bulkScale
  rw [←Real.rpow_mul_natCast (Nat.cast_nonneg N)]
  norm_num

lemma bulkScale_sq_shift_bound (n L : ℕ) :
    |bulkScale (n+1+L)^2-bulkScale (n+1)^2|≤
      (3/4:ℝ)*(L:ℝ)*((n+1:ℕ):ℝ)^(-(1:ℝ)/4) := by
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  have hd (x : ℝ) (hx : x∈Icc ((n+1:ℕ):ℝ) ((n+1+L:ℕ):ℝ)) :
      HasDerivWithinAt (fun x : ℝ=>x^((3:ℝ)/4))
        ((3/4:ℝ)*x^(-(1:ℝ)/4)) (Icc ((n+1:ℕ):ℝ) ((n+1+L:ℕ):ℝ)) x := by
    simpa only [show (3:ℝ)/4-1=-(1:ℝ)/4 by norm_num] using
      (Real.hasDerivAt_rpow_const (p:=(3:ℝ)/4) (Or.inl (ne_of_gt (hn.trans_le hx.1)))).hasDerivWithinAt
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun x hx=>show ‖(3/4:ℝ)*x^(-(1:ℝ)/4)‖≤(3/4:ℝ)*((n+1:ℕ):ℝ)^(-(1:ℝ)/4) by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (hn.trans_le hx.1).le _))]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hn hx.1 (by norm_num)) (by norm_num))
    (convex_Icc _ _)
    (show ((n+1:ℕ):ℝ)∈Icc ((n+1:ℕ):ℝ) ((n+1+L:ℕ):ℝ) by constructor; rfl; exact_mod_cast Nat.le_add_right (n+1) L)
    (show ((n+1+L:ℕ):ℝ)∈Icc ((n+1:ℕ):ℝ) ((n+1+L:ℕ):ℝ) by constructor; exact_mod_cast Nat.le_add_right (n+1) L; rfl)
  rw [bulkScale_sq_eq_rpow,bulkScale_sq_eq_rpow]
  simpa only [Real.norm_eq_abs,Nat.cast_add,add_sub_cancel_left,
    abs_of_nonneg (Nat.cast_nonneg L : (0:ℝ)≤L),mul_assoc,mul_comm,mul_left_comm] using hh

lemma bulkScale_sq_div_shift_bound (n L : ℕ) :
    bulkScale (n+1+L)^2/(n+1:ℕ)≤
      (L+1:ℝ)*((n+1:ℕ):ℝ)^(-(1:ℝ)/4) := by
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  have hNL : (0:ℝ)<(n+1+L:ℕ) := by positivity
  have he : bulkScale (n+1+L)^2=(n+1+L:ℕ)*((n+1+L:ℕ):ℝ)^(-(1:ℝ)/4) := by
    rw [bulkScale_sq_eq_rpow]
    calc
      _ = ((n+1+L:ℕ):ℝ)^((1:ℝ)+(-(1:ℝ)/4)) := by norm_num
      _ = _ := by rw [Real.rpow_add hNL,Real.rpow_one]
  rw [he]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ((n+1+L:ℕ):ℝ)*((n+1:ℕ):ℝ)^(-(1:ℝ)/4) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hn (by exact_mod_cast Nat.le_add_right (n+1) L) (by norm_num)) hNL.le
    _ ≤ _ := by
      have hb : ((n+1+L:ℕ):ℝ)≤(L+1:ℝ)*(n+1:ℕ) := by
        have h1 : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast Nat.succ_pos n
        push_cast
        nlinarith [mul_nonneg (Nat.cast_nonneg L) (show (0:ℝ)≤(n+1:ℕ)-1 by linarith)]
      nlinarith [mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hn.le (-(1:ℝ)/4))]

def cavityBulkCovarianceError (n L : ℕ) (C D : ℝ) : ℝ :=
  C^2*D*(bulkScale (n+1+L)^2/(n+1:ℕ))+
    bulkScale (n+1+L)^2*((L:ℝ)*C^2*(1/2:ℝ)^(n+1+1))+
    |bulkScale (n+1+L)^2-bulkScale (n+1)^2| * C^2

lemma cavityBulkCovarianceError_nonneg (n L : ℕ) (C : ℝ) {D : ℝ} (hD : 0≤D) :
    0≤cavityBulkCovarianceError n L C D := by unfold cavityBulkCovarianceError; positivity

lemma cavity_bulk_covariance_shell (n L : ℕ) (v : ℕ→ℝ) {C D r s : ℝ}
    (hC : 0≤C) (hD : 0≤D) (hv : ∀ j, |v (j+1)|≤C)
    (hr : |r|≤1) (hs : |s|≤1) (hδ : |s-r|≤D/(n+1:ℕ)) :
    |bulkScale (n+1+L)^2*bulkCovariance (n+1+L) v s-
      bulkScale (n+1)^2*bulkCovariance (n+1) v r|≤cavityBulkCovarianceError n L C D := by
  apply (cavity_bulk_covariance_bound (n+1) L v hC hv hr hs).trans
  unfold cavityBulkCovarianceError
  have ht : C^2*bulkScale (n+1+L)^2*|s-r|≤C^2*D*(bulkScale (n+1+L)^2/(n+1:ℕ)) := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul hδ (le_refl (C^2*bulkScale (n+1+L)^2)) (by positivity)
        (div_nonneg hD (by positivity))
  exact add_le_add (add_le_add ht le_rfl) le_rfl

lemma cavityBulkCovarianceError_tendsto (L : ℕ) (C : ℝ) {D : ℝ} (hD : 0≤D) :
    Tendsto (fun n=>cavityBulkCovarianceError n L C D) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hp : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)^(-(1:ℝ)/4)) atTop (𝓝 0) := by
    simpa only [neg_div,Function.comp_def] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp hN
  have hd : Tendsto (fun n=>C^2*D*(bulkScale (n+1+L)^2/(n+1:ℕ))) atTop (𝓝 0) :=
    squeeze_zero (fun n=>mul_nonneg (mul_nonneg (sq_nonneg C) hD) (by positivity))
      (fun n=>mul_le_mul_of_nonneg_left (bulkScale_sq_div_shift_bound n L)
        (mul_nonneg (sq_nonneg C) hD))
      (by simpa using (hp.const_mul (L+1:ℝ)).const_mul (C^2*D))
  have hs : Tendsto (fun n=>|bulkScale (n+1+L)^2-bulkScale (n+1)^2|) atTop (𝓝 0) :=
    squeeze_zero (fun n=>abs_nonneg _) (fun n=>bulkScale_sq_shift_bound n L)
      (by simpa using hp.const_mul ((3/4:ℝ)*(L:ℝ)))
  have hg : Tendsto (fun n : ℕ=>(1/2:ℝ)^(n+1+1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).comp
      ((tendsto_add_atTop_nat 1).comp (tendsto_add_atTop_nat 1))
  have hng : Tendsto (fun n : ℕ=>(n+1+1:ℕ)*(1/2:ℝ)^(n+1+1)) atTop (𝓝 0) := by
    simpa only [pow_one,Function.comp_def] using
      (tendsto_pow_const_mul_const_pow_of_lt_one 1 (by norm_num : (0:ℝ)≤1/2) (by norm_num)).comp
        ((tendsto_add_atTop_nat 1).comp (tendsto_add_atTop_nat 1))
  have hng' : Tendsto (fun n : ℕ=>(n+1+L:ℕ)*(1/2:ℝ)^(n+1+1)) atTop (𝓝 0) := by
    convert hng.add (hg.const_mul (L-1:ℝ)) using 1
    · ext n
      push_cast
      ring
    · simp
  have ht : Tendsto (fun n=>bulkScale (n+1+L)^2*(1/2:ℝ)^(n+1+1)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>by positivity) (fun n=>show _≤(n+1+L:ℕ)*(1/2:ℝ)^(n+1+1) from
      mul_le_mul_of_nonneg_right ?_ (by positivity)) hng'
    have hx : (1:ℝ)≤(n+1+L:ℕ) := by exact_mod_cast (by omega : 1≤n+1+L)
    rw [bulkScale_sq_eq_rpow]
    simpa using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (3:ℝ)/4≤1)
  convert (hd.add (ht.const_mul ((L:ℝ)*C^2))).add (hs.mul_const (C^2)) using 1
  · ext n
    unfold cavityBulkCovarianceError
    ring
  · simp
end SphericalPerceptronFreeEnergy
end

end OAI
