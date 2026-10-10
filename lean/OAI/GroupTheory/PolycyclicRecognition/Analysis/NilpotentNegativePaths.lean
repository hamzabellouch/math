import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentConjugationMetric
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PolynomialNegativePaths

namespace OAI

/-! # Negative-height paths in the nilpotent Cartan factor -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter Set
open scoped Manifold Topology

variable {E D G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace D] [ChartedSpace E D] [Group D]
  [LieGroup (𝓘(ℝ, E)) ⊤ D] [T2Space D]
  [Group G] [MetricSpace G] [IsIsometricSMul G G]

/-- A fixed Cartan displacement can be moved along a negative ray by
paths in a linear ball. Their coarse speeds grow only polynomially. -/
theorem exists_nilpotent_negative_paths
    (κ : D →* G) (hκ : Continuous κ)
    (dynkin : NilpotentDynkinExpansionInput E D)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) D → D) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) D ≃ₜ D) (hchart : ∀ x, chart x = Exp x)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) D)
      (GroupLieAlgebra (𝓘(ℝ, E)) D) c = ⊥)
    {m : ℕ} (b : Basis (Fin m) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) D))
    (η : G →* Multiplicative ℝ)
    (ℓ : GroupLieAlgebra (𝓘(ℝ, E)) D →ₗ[ℝ] ℝ)
    (hη : ∀ w, (η (κ (Exp w))).toAdd = ℓ w)
    (u v : GroupLieAlgebra (𝓘(ℝ, E)) D) (hv : ℓ v < 0) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧
      (∀ n : ℕ, dist 1 (κ (Exp ((n : ℝ) • v))) ≤ R * n) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ γ : Path (κ (Exp ((n : ℝ) • v))) (κ (Exp u) * κ (Exp ((n : ℝ) • v))),
          PathMetricBound γ (C * (1 + n) ^ c) C ∧
          (∀ t, (η (γ t)).toAdd ≤ (ℓ v / 2) * n) ∧
          ∀ t, dist 1 (γ t) ≤ R * n := by
  let _ : IsTopologicalGroup D := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  have hExpCont : Continuous Exp := by
    rw [← show chart = Exp from funext hchart]
    exact chart.continuous
  let Φ : (Fin m → ℝ) → G := fun w => κ (Exp (b.equivFun.symm w))
  obtain ⟨B, hB, hrad⟩ := continuous_radial_exponential_metric_bound Φ
    (hκ.comp (hExpCont.comp b.equivFun.symm.toContinuousLinearEquiv.continuous))
    (by simp [Φ, hExp.map_zero])
    (fun w s t => by simp only [Φ, map_smul, hExp.map_add_smul, map_mul])
  have hbound (w : GroupLieAlgebra (𝓘(ℝ, E)) D) :
      dist 1 (κ (Exp w)) ≤ B * (1 + ‖b.equivFun w‖) := by
    simpa only [Φ, b.equivFun.symm_apply_apply] using hrad (b.equivFun w)
  obtain ⟨C, hC, hmetric⟩ := exists_nilpotent_right_translate_coarse_metric
    κ hκ dynkin Exp hExp chart hchart hc b u v
  let R := B * (2 + ‖b.equivFun u‖ + ‖b.equivFun v‖)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hbase (n : ℕ) : dist 1 (κ (Exp ((n : ℝ) • v))) ≤ R * n := by
    have hh := one_parameter_nat_dist_le (fun t : ℝ => κ (Exp (t • v)))
      (by simp [hExp.map_zero]) (fun s t => by rw [hExp.map_add_smul, map_mul]) n
    have h1 : dist 1 (κ (Exp v)) ≤ R := by
      have hb := hbound v
      change dist 1 (κ (Exp v)) ≤ B * (2 + ‖b.equivFun u‖ + ‖b.equivFun v‖)
      nlinarith [norm_nonneg (b.equivFun u)]
    have hh' : dist 1 (κ (Exp ((n : ℝ) • v))) ≤ (n : ℝ) * dist 1 (κ (Exp v)) := by
      simpa only [one_smul] using hh
    exact (hh'.trans (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) n))).trans_eq (mul_comm _ _)
  refine ⟨C, R, hC, hR, hbase, ?_⟩
  have herr : ∀ᶠ n : ℕ in atTop, |ℓ u| ≤ (-ℓ v / 2) * n := by
    have ht := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop
      (show 0 < -ℓ v / 2 by linarith)
    exact ht.eventually (eventually_ge_atTop _)
  filter_upwards [herr, eventually_ge_atTop (1 : ℕ)] with n he hn1
  let γ : Path (κ (Exp ((n : ℝ) • v))) (κ (Exp u) * κ (Exp ((n : ℝ) • v))) := {
    toFun := fun t => κ (Exp ((t : ℝ) • u) * Exp ((n : ℝ) • v))
    continuous_toFun := hκ.comp ((hExpCont.comp (continuous_subtype_val.smul continuous_const)).mul continuous_const)
    source' := by simp [hExp.map_zero]
    target' := by simp }
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro s t
    change dist (κ (Exp ((s : ℝ) • u) * Exp ((n : ℝ) • v)))
      (κ (Exp ((t : ℝ) • u) * Exp ((n : ℝ) • v))) ≤ _
    have hs : |(t : ℝ) - s| ≤ 1 := abs_le.mpr ⟨by linarith [s.property.2, t.property.1],
      by linarith [s.property.1, t.property.2]⟩
    simpa only [abs_sub_comm] using hmetric n s t hs
  · intro t
    change (η (κ (Exp ((t : ℝ) • u) * Exp ((n : ℝ) • v)))).toAdd ≤ _
    rw [map_mul, map_mul, toAdd_mul, hη, hη, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have htu : (t : ℝ) * ℓ u ≤ |ℓ u| := by
      calc
        _ ≤ |(t : ℝ) * ℓ u| := le_abs_self _
        _ = (t : ℝ) * |ℓ u| := by rw [abs_mul, abs_of_nonneg t.property.1]
        _ ≤ |ℓ u| := by nlinarith [t.property.2, abs_nonneg (ℓ u)]
    nlinarith
  · intro t
    change dist 1 (κ (Exp ((t : ℝ) • u) * Exp ((n : ℝ) • v))) ≤ _
    rw [map_mul]
    have htri := dist_triangle (1 : G) (κ (Exp ((t : ℝ) • u)))
      (κ (Exp ((t : ℝ) • u)) * κ (Exp ((n : ℝ) • v)))
    have hd : dist (κ (Exp ((t : ℝ) • u)))
        (κ (Exp ((t : ℝ) • u)) * κ (Exp ((n : ℝ) • v))) =
        dist 1 (κ (Exp ((n : ℝ) • v))) := by
      simpa only [mul_one] using dist_mul_left (κ (Exp ((t : ℝ) • u))) (1 : G) _
    rw [hd] at htri
    have hu := hbound ((t : ℝ) • u)
    have hnv := hbound ((n : ℝ) • v)
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1] at hu
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)] at hnv
    have htu : (t : ℝ) * ‖b.equivFun u‖ ≤ ‖b.equivFun u‖ := mul_le_of_le_one_left (norm_nonneg _) t.property.2
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hbu := mul_le_mul_of_nonneg_left htu hB
    have hbu' := mul_le_mul_of_nonneg_left hn1' (mul_nonneg hB (norm_nonneg (b.equivFun u)))
    have hb' := mul_le_mul_of_nonneg_left hn1' hB
    change _ ≤ B * (2 + ‖b.equivFun u‖ + ‖b.equivFun v‖) * n
    nlinarith

end PolycyclicRecognition

end

end OAI
