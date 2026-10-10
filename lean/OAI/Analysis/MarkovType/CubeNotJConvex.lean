import OAI.Analysis.MarkovType.JConvexityBasic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def cutSignColumn {n : ℕ} (j : Fin n) : Fin n → ℝ := fun r => cutSign r j

theorem norm_cutSignColumn_le {n : ℕ} (j : Fin n) : ‖cutSignColumn j‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro r
  exact (norm_cutSign r j).le

theorem cutSum_cutSignColumn_diag {n : ℕ} (r : Fin n) :
    cutSum (fun j : Fin n => cutSignColumn j) r r = (n : ℝ) := by
  change (∑ j : Fin n, cutSign r j • cutSignColumn j) r = (n : ℝ)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cutSignColumn]
  calc
    ∑ j : Fin n, cutSign r j * cutSign r j = ∑ _j : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold cutSign
      split_ifs <;> norm_num
    _ = (n : ℝ) := by simp

theorem length_le_norm_cutSum_cutSignColumn {n : ℕ} (r : Fin n) :
    (n : ℝ) ≤ ‖cutSum (fun j : Fin n => cutSignColumn j) r‖ := by
  have h := norm_le_pi_norm (cutSum (fun j : Fin n => cutSignColumn j) r) r
  rw [cutSum_cutSignColumn_diag, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)] at h
  exact h

theorem not_ambientJConvex_of_nearIsometric_cubes
    (hcopies : ∀ (n : ℕ) (η : ℝ), 0 < η →
      ∃ T : (Fin n → ℝ) →ₗ[ℝ] X, ∀ a,
        ‖a‖ ≤ ‖T a‖ ∧ ‖T a‖ ≤ (1 + η) * ‖a‖) :
    ¬ AmbientJConvex X := by
  intro hJ
  obtain ⟨n, hn, δ, hδ, hδ1, hw⟩ := hJ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let c : ℝ := 1 + δ / 2
  have hc : 0 < c := by dsimp only [c]; linarith
  obtain ⟨T, hT⟩ := hcopies n (δ / 2) (by linarith)
  let y : Fin n → X := fun j => c⁻¹ • T (cutSignColumn j)
  have hy (j : Fin n) : ‖y j‖ ≤ 1 := by
    change ‖c⁻¹ • T (cutSignColumn j)‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    calc
      c⁻¹ * ‖T (cutSignColumn j)‖ ≤ c⁻¹ * (c * ‖cutSignColumn j‖) :=
        mul_le_mul_of_nonneg_left (hT _).2 (inv_nonneg.mpr hc.le)
      _ = ‖cutSignColumn j‖ := by
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ 1 := norm_cutSignColumn_le j
  obtain ⟨r, hr⟩ := hw y hy
  have hsum : T (cutSum (fun j : Fin n => cutSignColumn j) r) = c • cutSum y r := by
    rw [map_cutSum]
    dsimp only [y]
    rw [cutSum_smul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hlower : (n : ℝ) ≤ c * ‖cutSum y r‖ := by
    calc
      (n : ℝ) ≤ ‖cutSum (fun j : Fin n => cutSignColumn j) r‖ :=
        length_le_norm_cutSum_cutSignColumn r
      _ ≤ ‖T (cutSum (fun j : Fin n => cutSignColumn j) r)‖ := (hT _).1
      _ = c * ‖cutSum y r‖ := by
        rw [hsum, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hgap : c * (1 - δ) < 1 := by
    dsimp only [c]
    nlinarith [sq_nonneg δ]
  have hbad : (n : ℝ) < n := by
    calc
      (n : ℝ) ≤ c * ‖cutSum y r‖ := hlower
      _ ≤ c * ((n : ℝ) * (1 - δ)) := mul_le_mul_of_nonneg_left hr hc.le
      _ = (n : ℝ) * (c * (1 - δ)) := by ring
      _ < (n : ℝ) * 1 := mul_lt_mul_of_pos_left hgap hn0
      _ = (n : ℝ) := mul_one _
  exact (lt_irrefl (n : ℝ)) hbad

end MarkovSuperreflexivity

end

end OAI
