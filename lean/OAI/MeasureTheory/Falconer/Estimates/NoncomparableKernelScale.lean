import OAI.MeasureTheory.Falconer.Angular.NoncomparableSphereKernel

namespace OAI

/-! # Uniform powers for noncomparable radial kernels

The radial integration-by-parts order and the stationary expansion order
remain explicit. These scalar estimates convert their two different errors
to one prescribed power of the ambient scale.
-/

namespace Falconer

theorem exists_noncomparable_orders (m : ℕ) {κ loss : ℝ} (hκ : 0 < κ) :
    ∃ J q : ℕ, 1 ≤ J ∧ loss ≤ κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) ∧
      -κ*(J:ℝ)+2*(m+3) ≤ -loss := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((loss+2*(m+3))/κ)
  have hmul : loss+2*(m+3) < (n:ℝ)*κ := (div_lt_iff₀ hκ).mp hn
  refine ⟨n+1,n+1,by omega,?_,?_⟩
  · have hm : 0 ≤ ((m+2:ℕ):ℝ)/2 := by positivity
    have hd : 0 ≤ (m:ℝ)+3 := by positivity
    push_cast
    push_cast at hm
    nlinarith
  · push_cast
    nlinarith

theorem noncomparable_leading_decay_eq (m q : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) :
    Λ^(-((m+2:ℕ):ℝ)/2)/(Λ/2)^q =
      (2:ℝ)^q*Λ^(-((m+2:ℕ):ℝ)/2-(q:ℝ)) := by
  rw [show -((m+2:ℕ):ℝ)/2-(q:ℝ) =
    -((m+2:ℕ):ℝ)/2+(-(q:ℝ)) by ring,
    Real.rpow_add hΛ, Real.rpow_neg hΛ.le, Real.rpow_natCast, div_pow]
  field_simp

theorem noncomparable_leading_scale (m q : ℕ) {R Λ κ : ℝ}
    (hR : 0 < R) (hΛ : R^κ ≤ Λ) :
    Λ^(-((m+2:ℕ):ℝ)/2)/(Λ/2)^q ≤
      (2:ℝ)^q*R^(-κ*(((m+2:ℕ):ℝ)/2+(q:ℝ))) := by
  have hp : 0 < R^κ := Real.rpow_pos_of_pos hR _
  have h := noncomparable_leading_decay_mono m q hp hΛ
  rw [noncomparable_leading_decay_eq m q hp] at h
  apply h.trans_eq
  congr 1
  rw [← Real.rpow_mul hR.le]
  congr 1
  ring

theorem noncomparable_stationary_error_scale {R exponent loss W S C M : ℝ}
    (hR : 1 ≤ R) (hloss : 0 ≤ loss) (hexponent : exponent ≤ -loss)
    (hW : 0 ≤ W) (hS : 0 ≤ S) (hC : 0 ≤ C) (hM : 0 ≤ M) :
    4*W*((S*C*R^exponent)*(2*M+S*C*R^exponent)) ≤
      (4*W*S*C*(2*M+S*C))*R^(-loss) := by
  have hpow : R^exponent ≤ R^(-loss) := Real.rpow_le_rpow_of_exponent_le hR hexponent
  have hunit : R^(-loss) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (neg_nonpos.mpr hloss)
  have hSC : 0 ≤ S*C := mul_nonneg hS hC
  have he : S*C*R^exponent ≤ S*C*R^(-loss) :=
    mul_le_mul_of_nonneg_left hpow hSC
  have heunit : S*C*R^exponent ≤ S*C :=
    he.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hunit hSC)
  calc
    _ ≤ 4*W*((S*C*R^(-loss))*(2*M+S*C)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul he (add_le_add le_rfl heunit) (by positivity) (by positivity))
        (by positivity)
    _ = _ := by ring

theorem noncomparable_kernel_scale {m J q : ℕ} {R Λ κ loss H W S C E M : ℝ}
    (hR : 1 ≤ R) (hΛ : R^κ ≤ Λ) (hloss : 0 ≤ loss)
    (hleading : loss ≤ κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)))
    (hexponent : -κ*(J:ℝ)+2*(m+3) ≤ -loss)
    (hH : 0 ≤ H) (hW : 0 ≤ W) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (hM : 0 ≤ M) :
    H*C*E*M*Λ^(-((m+2:ℕ):ℝ)/2)/(Λ/2)^q +
        4*W*((S*C*R^(-κ*(J:ℝ)+2*(m+3)))*
          (2*(max C E*M)+S*C*R^(-κ*(J:ℝ)+2*(m+3)))) ≤
      (H*C*E*M*(2:ℝ)^q + 4*W*S*C*(2*(max C E*M)+S*C))*R^(-loss) := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hc : 0 ≤ H*C*E*M := by positivity
  have hdecay := noncomparable_leading_scale m q hRpos hΛ
  have hpower : R^(-κ*(((m+2:ℕ):ℝ)/2+(q:ℝ))) ≤ R^(-loss) :=
    Real.rpow_le_rpow_of_exponent_le hR (by simpa only [neg_mul] using neg_le_neg hleading)
  have hleadingBound : H*C*E*M*Λ^(-((m+2:ℕ):ℝ)/2)/(Λ/2)^q ≤
      (H*C*E*M*(2:ℝ)^q)*R^(-loss) := by
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left hdecay hc).trans
      (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hpower
        (mul_nonneg hc (pow_nonneg (by norm_num) q))))
  have herror := noncomparable_stationary_error_scale (M := max C E*M)
    hR hloss hexponent hW hS hC (mul_nonneg (hC.trans (le_max_left C E)) hM)
  calc
    _ ≤ _ := add_le_add hleadingBound herror
    _ = _ := by ring

end Falconer

end OAI
