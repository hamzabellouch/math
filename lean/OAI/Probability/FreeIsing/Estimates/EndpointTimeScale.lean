import OAI.Probability.FreeIsing.Estimates.EndpointScale

namespace OAI

noncomputable section

namespace Problem367

theorem inv_sqrt_sq_time {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t)⁻¹ ^ 2 = 1 / t := by
  rw [inv_pow, Real.sq_sqrt ht, one_div]

theorem mul_sqrt_eq_three_halves {x : ℝ} (hx : 0 ≤ x) :
    x * Real.sqrt x = x ^ ((3 : ℝ) / 2) := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · norm_num
  calc
    x * Real.sqrt x = x ^ (1 : ℝ) * x ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_one, Real.sqrt_eq_rpow]
    _ = x ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hx _ _).symm
    _ = x ^ ((3 : ℝ) / 2) := by norm_num

theorem inv_sqrt_mul_sqrt_time {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t)⁻¹ * Real.sqrt ((Real.sqrt t)⁻¹) = t ^ (-(3 : ℝ) / 4) := by
  rw [mul_sqrt_eq_three_halves (by positivity), Real.sqrt_eq_rpow,
    ← Real.rpow_neg_one, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le]
  norm_num

theorem inv_sqrt_le_time_three_quarters {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (Real.sqrt t)⁻¹ ≤ t ^ (-(3 : ℝ) / 4) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs1 : Real.sqrt t ≤ 1 := by
    simpa using Real.sqrt_le_sqrt ht1
  have hi : 1 ≤ (Real.sqrt t)⁻¹ := (one_le_inv₀ hs).2 hs1
  have hsqrt1 : 1 ≤ Real.sqrt ((Real.sqrt t)⁻¹) := by
    simpa using Real.sqrt_le_sqrt hi
  rw [← inv_sqrt_mul_sqrt_time ht]
  simpa using mul_le_mul_of_nonneg_left hsqrt1 (inv_nonneg.2 hs.le)

theorem quadratic_endpoint_time_scale {F A B E S V R K I t : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hR0 : 0 ≤ R) (hK : 0 ≤ K) (hI : 1 ≤ I) (ht : 0 < t)
    (hR : R ≤ K * ((Real.sqrt t)⁻¹ + Real.log I))
    (hF : F ≤ A * S * R ^ 2 + B * S * (1 / t) + E * V ^ 2) :
    F ≤ max (2 * A * K ^ 2 + B) E *
      (S * (1 / t + (Real.log I) ^ 2) + V ^ 2) := by
  have hs := quadratic_endpoint_scale (F := F) (E := E) (V := V) hA hB hS hR0 hK
    (show 0 ≤ (Real.sqrt t)⁻¹ by positivity) (Real.log_nonneg hI) hR
  rw [inv_sqrt_sq_time ht.le] at hs
  exact hs hF

theorem linear_endpoint_time_scale {F A B E V R K I t : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hV : 0 ≤ V) (hK : 0 ≤ K)
    (hI : 1 ≤ I) (ht : 0 < t) (ht1 : t ≤ 1)
    (hR : R ≤ K * ((Real.sqrt t)⁻¹ + Real.log I))
    (hF : F ≤ A * V * R + B * V * (Real.sqrt t)⁻¹ + E * V ^ 2) :
    F ≤ max (A * K + B) E *
      (V * (t ^ (-(3 : ℝ) / 4) + Real.log I) + V ^ 2) := by
  have hscale := linear_endpoint_scale hA hB hV
    (show 0 ≤ (Real.sqrt t)⁻¹ by positivity) (Real.log_nonneg hI) hR hF
  have hC : 0 ≤ max (A * K + B) E :=
    (add_nonneg (mul_nonneg hA hK) hB).trans (le_max_left _ _)
  apply hscale.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ hV
  exact add_le_add (inv_sqrt_le_time_three_quarters ht ht1) le_rfl

theorem sqrt_endpoint_time_scale {F A B E S V R K I t : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hR0 : 0 ≤ R) (hK : 0 ≤ K) (hI : 1 ≤ I) (ht : 0 < t)
    (hR : R ≤ K * ((Real.sqrt t)⁻¹ + Real.log I))
    (hF : F ≤ A * Real.sqrt S * (R * Real.sqrt R) +
      B * Real.sqrt S * t ^ (-(3 : ℝ) / 4) + E * V) :
    F ≤ max (4 * A * K * Real.sqrt K + B) E *
      (Real.sqrt S * (t ^ (-(3 : ℝ) / 4) + (Real.log I) ^ ((3 : ℝ) / 2)) + V) := by
  have hs := sqrt_endpoint_scale (F := F) (E := E) (S := S) hA hB hV hR0 hK
    (show 0 ≤ (Real.sqrt t)⁻¹ by positivity) (Real.log_nonneg hI) hR
  rw [inv_sqrt_mul_sqrt_time ht, mul_sqrt_eq_three_halves (Real.log_nonneg hI)] at hs
  exact hs hF

def endpointTimeConstant (A B E K : ℝ) : ℝ :=
  max 1 (max (max (2 * A * K ^ 2 + B) E)
    (max (max (A * K + B) E) (max (4 * A * K * Real.sqrt K + B) E)))

theorem endpointTimeConstant_ge_one (A B E K : ℝ) :
    1 ≤ endpointTimeConstant A B E K := le_max_left _ _

theorem endpoint_time_scales {Q L Z A B E S V R K I t C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S) (hV : 0 ≤ V)
    (hR0 : 0 ≤ R) (hK : 0 ≤ K) (hI : 1 ≤ I) (ht : 0 < t) (ht1 : t ≤ 1)
    (hC : endpointTimeConstant A B E K ≤ C)
    (hR : R ≤ K * ((Real.sqrt t)⁻¹ + Real.log I))
    (hQ : Q ≤ A * S * R ^ 2 + B * S * (1 / t) + E * V ^ 2)
    (hL : L ≤ A * V * R + B * V * (Real.sqrt t)⁻¹ + E * V ^ 2)
    (hZ : Z ≤ A * Real.sqrt S * (R * Real.sqrt R) +
      B * Real.sqrt S * t ^ (-(3 : ℝ) / 4) + E * V) :
    Q ≤ C * (S * (1 / t + (Real.log I) ^ 2) + V ^ 2) ∧
    L ≤ C * (V * (t ^ (-(3 : ℝ) / 4) + Real.log I) + V ^ 2) ∧
    Z ≤ C * (Real.sqrt S *
      (t ^ (-(3 : ℝ) / 4) + (Real.log I) ^ ((3 : ℝ) / 2)) + V) := by
  have hQC : max (2 * A * K ^ 2 + B) E ≤ C := by
    apply le_trans _ hC
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hLC : max (A * K + B) E ≤ C := by
    apply le_trans _ hC
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hZC : max (4 * A * K * Real.sqrt K + B) E ≤ C := by
    apply le_trans _ hC
    exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hlog : 0 ≤ Real.log I := Real.log_nonneg hI
  refine ⟨?_, ?_, ?_⟩
  · exact (quadratic_endpoint_time_scale hA hB hS hR0 hK hI ht hR hQ).trans
      (mul_le_mul_of_nonneg_right hQC (by positivity))
  · exact (linear_endpoint_time_scale hA hB hV hK hI ht ht1 hR hL).trans
      (mul_le_mul_of_nonneg_right hLC (by positivity))
  · exact (sqrt_endpoint_time_scale hA hB hV hR0 hK hI ht hR hZ).trans
      (mul_le_mul_of_nonneg_right hZC (by positivity))

end Problem367

end

end OAI
