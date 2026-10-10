import OAI.MeasureTheory.Falconer.Graphs.GraphFourTransformExpansion

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graph_four_spatial_ae_carrier (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (hX : ∀ i, MeasurableSet (X i)) :
    ∀ᵐ x ∂Measure.pi (fun i => (ρ i).restrict (X i)), ∀ i, x i ∈ X i := by
  apply Filter.eventually_all.mpr
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem (hX i))

theorem normalized_four_integral_norm_le (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (hX : ∀ i, MeasurableSet (X i))
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 < M i) (F : (Fin 4 → Plane) → ℂ) {ε : ℝ}
    (hb : ∀ x, (∀ i, x i ∈ X i) → ‖F x‖ ≤ ε) :
    ‖((M 0*M 1)*(M 2*M 3))⁻¹ • (∫ x, F x ∂Measure.pi (fun i => (ρ i).restrict (X i)))‖ ≤
      ε * ∏ i : Fin 4, (ρ i (X i)).toReal / M i := by
  let μ := Measure.pi (fun i => (ρ i).restrict (X i))
  have he : ∀ᵐ x ∂μ, ‖F x‖ ≤ ε := (graph_four_spatial_ae_carrier ρ X hX).mono (fun x hx => hb x hx)
  have hi := norm_integral_le_of_norm_le_const he
  have hm : μ.real univ = ∏ i : Fin 4, (ρ i (X i)).toReal := by
    simp only [μ,Measure.real,Measure.pi_univ,Measure.restrict_apply_univ,ENNReal.toReal_prod]
  rw [hm] at hi
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (mul_pos (mul_pos (hM 0) (hM 1)) (mul_pos (hM 2) (hM 3))))]
  apply (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (mul_nonneg (mul_pos (hM 0) (hM 1)).le (mul_pos (hM 2) (hM 3)).le))).trans_eq
  simp only [Fin.prod_univ_four,div_eq_mul_inv,mul_inv_rev]
  ring

theorem normalized_four_integral_power_le (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (hX : ∀ i, MeasurableSet (X i))
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 < M i) (F : (Fin 4 → Plane) → ℂ)
    {R lam U : ℝ} (hR : 0 < R)
    (hb : ∀ x, (∀ i, x i ∈ X i) → ‖F x‖ ≤ R^(-U))
    (hm : ∀ i, (ρ i (X i)).toReal / M i ≤ R^(3*lam)) :
    ‖((M 0*M 1)*(M 2*M 3))⁻¹ • (∫ x, F x ∂Measure.pi (fun i => (ρ i).restrict (X i)))‖ ≤
      R^(-U+12*lam) := by
  apply (normalized_four_integral_norm_le ρ X hX M hM F hb).trans
  have hprod : (∏ i : Fin 4, (ρ i (X i)).toReal / M i) ≤ ∏ _i : Fin 4, R^(3*lam) :=
    Finset.prod_le_prod₀ (fun i _ => div_nonneg ENNReal.toReal_nonneg (hM i).le) (fun i _ => hm i)
  calc
    _ ≤ R^(-U)*(∏ _i : Fin 4, R^(3*lam)) := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = R^(-U+12*lam) := by
      simp only [Fin.prod_univ_four,← Real.rpow_add hR]
      congr 1
      ring

end PlanarFalconer

end OAI
