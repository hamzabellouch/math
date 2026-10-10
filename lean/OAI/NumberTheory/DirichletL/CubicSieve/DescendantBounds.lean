import OAI.NumberTheory.DirichletL.CubicSieve.CommonFactorBound

namespace OAI

namespace SevenEighths.CubicSieve
noncomputable section

lemma descendant_cross_le (M N D E : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) :
    ((M/E)*(N/D))^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  exact mul_le_mul (div_le_self hM hE) (div_le_self hN hD) (by positivity) hM

lemma descendant_asymmetric_le (M N D E ξ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hED : E ≤ D) (hξ : 1 ≤ ξ) :
    (M/E)^(1-ξ)*(N/D)^(2*ξ-1) ≤ M^(1-ξ)*N^(2*ξ-1) := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hp : E^(ξ-1) ≤ D^(2*ξ-1) :=
    (Real.rpow_le_rpow hE0.le hED (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hD (by linarith))
  have hr : E^(ξ-1)/D^(2*ξ-1) ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hD0 _)).mpr hp
  have he : E^(1-ξ) = (E^(ξ-1))⁻¹ := by
    rw [← Real.rpow_neg hE0.le]
    congr 1
    ring
  calc
    _ = (M^(1-ξ)*N^(2*ξ-1))*(E^(ξ-1)/D^(2*ξ-1)) := by
      rw [Real.div_rpow hM.le hE0.le, Real.div_rpow hN.le hD0.le, he]
      simp only [div_eq_mul_inv, inv_inv]
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hr

lemma descendant_loss_le (M N D E δ ε : ℝ) (hM : 1 ≤ M) (hN : 0 < N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hED : E ≤ D) (hDN : D ≤ N)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    (M/E)^(-δ)*(N/D)^(3*δ+ε) ≤ N^(4*δ+ε) := by
  have hM0 : 0 < M := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hEM : E/M ≤ N := (div_le_self hE0.le hM).trans (hED.trans hDN)
  have hfirst : (M/E)^(-δ) ≤ N^δ := by
    rw [Real.rpow_neg (div_pos hM0 hE0).le, ← Real.inv_rpow (div_pos hM0 hE0).le, inv_div]
    exact Real.rpow_le_rpow (by positivity) hEM hδ
  have hsecond : (N/D)^(3*δ+ε) ≤ N^(3*δ+ε) :=
    Real.rpow_le_rpow (by positivity) (div_le_self hN.le hD) (by positivity)
  calc
    _ ≤ N^δ*N^(3*δ+ε) := mul_le_mul hfirst hsecond (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hN]
      congr 1
      ring

lemma descendant_unit_scale_le (M N D E : ℝ) (hM : 0 ≤ M) (hN : 0 < N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hDN : D ≤ N) :
    (M/E)*(2/(N/D)) ≤ 2*M := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hY : 1 ≤ N/D := (one_le_div hD0).mpr hDN
  have hr : 2/(N/D) ≤ 2 := div_le_self (by norm_num) hY
  calc
    _ ≤ M*2 := mul_le_mul (div_le_self hM hE) hr (by positivity) hM
    _ = _ := mul_comm _ _

end
end SevenEighths.CubicSieve

end OAI
