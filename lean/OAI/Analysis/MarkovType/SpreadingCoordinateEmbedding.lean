import OAI.Analysis.MarkovType.SpreadingLimitUniform
import OAI.Analysis.MarkovType.SpreadingLimitEmbedding
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem relative_error_of_cube_error {m : ℕ} (p : Seminorm ℝ (Fin m → ℝ))
    (S : (Fin m → ℝ) →ₗ[ℝ] Y) (d δ : ℝ) (_hd : 0 < d) (hδ : 0 ≤ δ)
    (hcoord : ∀ a i, (d / 2) * |a i| ≤ p a)
    (hcube : ∀ a, (∀ i, |a i| ≤ 1) →
      |‖S a‖ - p a| ≤ δ * (d / 2) / ((m : ℝ) + 1)) :
    ∀ a, |‖S a‖ - p a| ≤ δ * p a := by
  classical
  intro a
  let c : ℝ := ∑ i, |a i|
  have hc0 : 0 ≤ c := Finset.sum_nonneg (fun i _ => abs_nonneg (a i))
  have hsingle (i : Fin m) : |a i| ≤ c :=
    Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
  by_cases hc : c = 0
  · have ha : a = 0 := by
      funext i
      have hi := hsingle i
      rw [hc] at hi
      exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
    simp [ha]
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
  let b : Fin m → ℝ := c⁻¹ • a
  have hab : c • b = a := by
    simp only [b, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hb : ∀ i, |b i| ≤ 1 := by
    intro i
    change |c⁻¹ * a i| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.mpr hcpos)]
    calc
      c⁻¹ * |a i| ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left (hsingle i) (inv_nonneg.mpr hc0)
      _ = 1 := inv_mul_cancel₀ hc
  have hscale : |‖S a‖ - p a| = c * |‖S b‖ - p b| := by
    conv_lhs => rw [← hab]
    rw [map_smul, norm_smul, map_smul_eq_mul p, Real.norm_of_nonneg hc0,
      ← mul_sub, abs_mul, abs_of_nonneg hc0]
  have hmass : (d / 2) * c ≤ (m : ℝ) * p a := by
    calc
      (d / 2) * c = ∑ i, (d / 2) * |a i| := Finset.mul_sum _ _ _
      _ ≤ ∑ _i : Fin m, p a := Finset.sum_le_sum (fun i _ => hcoord a i)
      _ = (m : ℝ) * p a := by simp
  have hmpos : 0 < (m : ℝ) + 1 := by positivity
  have hmass' : (d / 2) * c ≤ ((m : ℝ) + 1) * p a := by
    have hp := apply_nonneg p a
    nlinarith
  rw [hscale]
  calc
    c * |‖S b‖ - p b| ≤ c * (δ * (d / 2) / ((m : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (hcube b hb) hc0
    _ = δ * ((d / 2) * c) / ((m : ℝ) + 1) := by ring
    _ ≤ δ * (((m : ℝ) + 1) * p a) / ((m : ℝ) + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass' hδ) hmpos.le
    _ = δ * p a := by field_simp [hmpos.ne']

theorem exists_coordinate_embedding_of_convergence {m : ℕ}
    (p : Seminorm ℝ (Fin m → ℝ)) (d : ℝ) (hd : 0 < d)
    (hcoord : ∀ a i, (d / 2) * |a i| ≤ p a)
    (L : ℕ → (Fin m → ℝ) →ₗ[ℝ] Y)
    (hlip : ∀ n a b, |‖L n a‖ - ‖L n b‖| ≤ ∑ i, |a i - b i|)
    (hlim : ∀ a, Tendsto (fun n => ‖L n a‖) atTop (𝓝 (p a)))
    (η : ℝ) (hη : 0 < η) :
    ∃ T : (Fin m → ℝ) →ₗ[ℝ] Y, ∀ a,
      p a ≤ ‖T a‖ ∧ ‖T a‖ ≤ (1 + η) * p a := by
  let δ : ℝ := η / (2 + η)
  have hδ : 0 < δ := div_pos hη (by linarith)
  let ε : ℝ := δ * (d / 2) / ((m : ℝ) + 1)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨N, hN⟩ := uniform_coefficients_of_pointwise
    (fun n a => ‖L n a‖) p hlip hlim ε hε
  apply exists_spreading_normalizedMap p (L N) η hη
  apply relative_error_of_cube_error p (L N) d δ hd hδ.le hcoord
  intro a ha
  exact (hN N le_rfl a ha).le

end MarkovSuperreflexivity

end

end OAI
