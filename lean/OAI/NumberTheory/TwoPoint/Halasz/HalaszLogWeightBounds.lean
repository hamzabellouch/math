import OAI.NumberTheory.TwoPoint.Halasz.HalaszLogWeights

namespace OAI

/-! The coordinate saving follows from the three elementary scale ratios. -/
namespace TwoPointCorrelations

lemma halasz_log_weight_bound {k r M : ℕ} (hr : 1≤r) (hM : 1≤M)
    {t z N A B E η : ℝ} (ht : t≠0) (hz : 0<z) (j : Fin k)
    (h₁ : 1/(M:ℝ)^(j.val+1)≤A*N^(-η))
    (h₂ : |t|/z^(j.val+1)≤B*N^(-η))
    (h₃ : z^(j.val+1)/(((M:ℝ)^(j.val+1))^2*|t|)≤E*N^(-η)) :
    halaszNormalizedWeight r M (halaszLogCoefficient t z) j ≤
      ((5/2:ℝ)*A+(r:ℝ)/(Real.pi*(j.val+1))*B+
        Real.pi*(j.val+1)/(r:ℝ)*E)*N^(-η) := by
  have hr0 : 0<(r:ℝ) := by exact_mod_cast (show 0<r by omega)
  have hj0 : 0<(j.val:ℝ)+1 := by positivity
  rw [halasz_log_weight_identity hr hM ht hz]
  apply (min_le_right _ _).trans
  have hh := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left h₁ (by norm_num : (0:ℝ)≤5/2))
    (mul_le_mul_of_nonneg_left h₂ (by positivity : 0≤(r:ℝ)/(Real.pi*(j.val+1)))))
    (mul_le_mul_of_nonneg_left h₃ (by positivity : 0≤Real.pi*(j.val+1)/(r:ℝ)))
  convert hh using 1
  · field_simp
  · ring

lemma halasz_three_degree_rates {N α lam d η : ℝ} (hN : 1≤N)
    (h₁ : η≤α*d) (h₂ : η≤d-lam) (h₃ : η≤lam-d+2*α*d) :
    N^(-α*d)≤N^(-η) ∧ N^(lam-d)≤N^(-η) ∧
      N^(d-2*α*d-lam)≤N^(-η) := by
  refine ⟨Real.rpow_le_rpow_of_exponent_le hN (by linarith),
    Real.rpow_le_rpow_of_exponent_le hN (by linarith),
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)⟩

end TwoPointCorrelations

end OAI
