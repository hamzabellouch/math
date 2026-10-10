import OAI.NumberTheory.Ostmann.Dirichlet.GrowthBase

namespace OAI

section
section IntroDependency0
section GrowthDependency1
open MeasureTheory Set
namespace Ostmann.Dirichlet

theorem integrableOn_min_mul_rpow {q r : ℝ} (hq : 0 ≤ q) (hr : r < -1) :
    IntegrableOn (fun x : ℝ => min x q * x ^ r) (Ioi 1) := by
  have hcont : ContinuousOn (fun x : ℝ => min x q * x ^ r) (Ioi 1) :=
    (continuous_id.min continuous_const).continuousOn.mul
      (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (lt_trans zero_lt_one hx))))
  apply ((integrableOn_Ioi_rpow_of_lt hr zero_lt_one).const_mul q).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := (lt_trans zero_lt_one hx).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_min hx0 hq) (Real.rpow_nonneg hx0 _))]
  exact mul_le_mul_of_nonneg_right (min_le_right x q) (Real.rpow_nonneg hx0 _)

end Ostmann.Dirichlet
end GrowthDependency1
end IntroDependency0
end

section
section IntroDependency0
section GrowthDependency1
open MeasureTheory Set
namespace Ostmann.Dirichlet

theorem integral_min_mul_rpow_exact {q η : ℝ} (hq : 1 ≤ q) (hη : 0 < η) (hη1 : η < 1) :
    (∫ x : ℝ in Ioi 1, min x q * x ^ (η - 2)) =
      (q ^ η - 1) / η + q ^ η / (1 - η) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr : η - 2 < -1 := by linarith
  have hint := integrableOn_min_mul_rpow hq0.le hr
  have hfirst : (∫ x : ℝ in 1..q, min x q * x ^ (η - 2)) = (q ^ η - 1) / η := by
    calc
      _ = ∫ x : ℝ in 1..q, x ^ (η - 1) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hq] at hx
        have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
        dsimp only
        rw [min_eq_left hx.2]
        calc
          _ = x ^ (1 + (η - 2)) := by rw [Real.rpow_add hx0, Real.rpow_one]
          _ = _ := by congr 1; ring
      _ = _ := by
        rw [integral_rpow (Or.inl (by linarith : -1 < η - 1))]
        simp only [show η - 1 + 1 = η by ring, Real.one_rpow]
  have htail : (∫ x : ℝ in Ioi q, min x q * x ^ (η - 2)) = q ^ η / (1 - η) := by
    calc
      _ = ∫ x : ℝ in Ioi q, q * x ^ (η - 2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only
        rw [min_eq_right hx.le]
      _ = q * (-q ^ (η - 2 + 1) / (η - 2 + 1)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt hr hq0]
      _ = _ := by
        have hp : q * q ^ (η - 1) = q ^ η := by
          calc
            _ = q ^ (1 + (η - 1)) := by rw [Real.rpow_add hq0, Real.rpow_one]
            _ = _ := by congr 1; ring
        rw [show η - 2 + 1 = η - 1 by ring]
        have hηn : η - 1 ≠ 0 := by linarith
        have hηn' : 1 - η ≠ 0 := by linarith
        field_simp
        nlinarith [hp]
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint
    (hint.mono_set (Ioi_subset_Ioi hq))
  rw [hfirst, htail] at hsplit
  exact hsplit.symm

end Ostmann.Dirichlet
end GrowthDependency1
end IntroDependency0
end

section
section IntroDependency0
section GrowthDependency1
open MeasureTheory Set
namespace Ostmann.Dirichlet

theorem integral_min_mul_rpow_le {q η σ : ℝ} (hq : 1 ≤ q) (hη : 0 < η)
    (hηhalf : η ≤ 1 / 2) (hσ : 1 - η ≤ σ) :
    (∫ x : ℝ in Ioi 1, min x q * x ^ (-σ - 1)) ≤ q ^ η * (1 / η + 2) := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  have hσ0 : 0 < σ := by linarith
  have hη1 : η < 1 := by linarith
  have hint := integrableOn_min_mul_rpow hq0 (by linarith : -σ - 1 < -1)
  have henv := integrableOn_min_mul_rpow hq0 (by linarith : η - 2 < -1)
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, min x q * x ^ (η - 2) := by
      apply integral_mono_ae hint henv
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
        (le_min (le_trans zero_le_one hx.le) hq0)
    _ = (q ^ η - 1) / η + q ^ η / (1 - η) := integral_min_mul_rpow_exact hq hη hη1
    _ ≤ q ^ η * (1 / η + 2) := by
      have hp : 0 ≤ q ^ η := Real.rpow_nonneg hq0 _
      have hfirst : (q ^ η - 1) / η ≤ q ^ η / η :=
        div_le_div_of_nonneg_right (by linarith) hη.le
      have htail : q ^ η / (1 - η) ≤ 2 * q ^ η := by
        apply (div_le_iff₀ (by linarith : 0 < 1 - η)).mpr
        nlinarith
      calc
        _ ≤ q ^ η / η + 2 * q ^ η := add_le_add hfirst htail
        _ = _ := by ring

end Ostmann.Dirichlet
end GrowthDependency1
end IntroDependency0
end

section
section IntroDependency0
namespace Ostmann.Dirichlet
open Finset MeasureTheory

theorem norm_sum_character_Icc_le_min {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)‖ ≤ min t (q : ℝ) := by
  apply le_min
  · calc
      ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)‖ ≤
          ∑ k ∈ Icc 1 ⌊t⌋₊, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Icc 1 ⌊t⌋₊, (1 : ℝ) := sum_le_sum fun k _ => χ.norm_le_one k
      _ = (⌊t⌋₊ : ℝ) := by simp
      _ ≤ t := Nat.floor_le ht
  · exact (norm_sum_character_Icc_lt χ hχ ⌊t⌋₊).le

end Ostmann.Dirichlet
end IntroDependency0
end

end OAI
