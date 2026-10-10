import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedComplexZeroDensity
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteLaplaceDensity

namespace OAI

/-! # The low-zero Laplace estimate from the published density theorem -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def lowZeroIndices (Z : ∀ χ, ComplexZeroEnumeration χ)
    (F : Finset PrimitiveComplexCharacter) (T : ℝ) : Finset (Σ _χ : PrimitiveComplexCharacter, ℕ) :=
  F.sigma fun χ => ((Z χ).heightIndices T).filter (fun i => 1 / 2 ≤ ((Z χ).zeros i).re)

theorem complex_zero_density_exponential
    (Z : ∀ χ, ComplexZeroEnumeration χ) {C : ℝ} (hC : 0 ≤ C)
    (hdensity : ∀ (Q : ℕ), 1 ≤ Q → ∀ (T σ : ℝ), 2 ≤ T →
      1 / 2 ≤ σ → σ ≤ 1 → ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ((Z χ).count σ T : ℝ)) ≤
        C * ((Q : ℝ) ^ 2 * T) ^ (3 * (1 - σ) / (2 - σ)) *
          (Real.log ((Q : ℝ) * T)) ^ 13)
    (Q : ℕ) (hQ : 1 ≤ Q) (T y : ℝ) (hT : 2 ≤ T) (hy : 0 ≤ y) (hy' : y ≤ 1 / 2)
    (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ ∈ F, χ.modulus ≤ Q) :
    (∑ χ ∈ F, ((Z χ).count (1 - y) T : ℝ)) ≤
      (C * (Real.log ((Q : ℝ) * T)) ^ 13) *
        Real.exp ((3 * Real.log ((Q : ℝ) ^ 2 * T)) * y) := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hbase : 1 ≤ (Q : ℝ) ^ 2 * T := by nlinarith
  have hlog : 0 ≤ Real.log ((Q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  have hexp : 3 * (1 - (1 - y)) / (2 - (1 - y)) ≤ 3 * y := by
    calc
      _ = 3 * y / (1 + y) := by congr 1 <;> ring
      _ ≤ 3 * y := div_le_self (by positivity) (by linarith)
  have hp := Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hd := hdensity Q hQ T (1 - y) hT (by linarith) (by linarith) F hF
  apply hd.trans
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC)
    (pow_nonneg hlog 13)
  have he : ((Q : ℝ) ^ 2 * T) ^ (3 * y) =
      Real.exp ((3 * Real.log ((Q : ℝ) ^ 2 * T)) * y) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < (Q : ℝ) ^ 2 * T)]
    congr 1
    ring
  rw [he] at hm
  convert hm using 1
  ring

theorem lowZeroIndices_count_bound
    (Z : ∀ χ, ComplexZeroEnumeration χ) (F : Finset PrimitiveComplexCharacter)
    (T A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hd : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 →
      (∑ χ ∈ F, ((Z χ).count (1 - y) T : ℝ)) ≤ B * Real.exp (A * y)) :
    ∀ t : ℝ, 0 ≤ t →
      (((lowZeroIndices Z F T).filter
        (fun z => 1 - ((Z z.1).zeros z.2).re ≤ t)).card : ℝ) ≤ B * Real.exp (A * t) := by
  intro t ht
  let y := min t (1 / 2 : ℝ)
  have hy : 0 ≤ y := le_min ht (by norm_num)
  have hy' : y ≤ 1 / 2 := min_le_right _ _
  have hsub : (lowZeroIndices Z F T).filter
      (fun z => 1 - ((Z z.1).zeros z.2).re ≤ t) ⊆
      F.sigma (fun χ => ((Z χ).heightIndices T).filter
        (fun i => 1 - y ≤ ((Z χ).zeros i).re)) := by
    intro z hz
    obtain ⟨hz, hgap⟩ := Finset.mem_filter.mp hz
    obtain ⟨hχ, hi⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hi, hre⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_sigma.mpr
    refine ⟨hχ, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
    have hh : 1 - ((Z z.1).zeros z.2).re ≤ y := le_min hgap (by linarith)
    linarith
  calc
    _ ≤ ((F.sigma (fun χ => ((Z χ).heightIndices T).filter
        (fun i => 1 - y ≤ ((Z χ).zeros i).re))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = ∑ χ ∈ F, ((Z χ).count (1 - y) T : ℝ) := by
      rw [Finset.card_sigma, Nat.cast_sum]
      rfl
    _ ≤ B * Real.exp (A * y) := hd y hy hy'
    _ ≤ B * Real.exp (A * t) := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (min_le_left _ _) hA)) hB

theorem low_zero_laplace_bound
    (Z : ∀ χ, ComplexZeroEnumeration χ) (F : Finset PrimitiveComplexCharacter)
    (T A B M u : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 4 * A ≤ M) (hu : 0 ≤ u)
    (hgap : ∀ χ ∈ F, ∀ i ∈ (Z χ).heightIndices T, u ≤ 1 - ((Z χ).zeros i).re)
    (hd : ∀ y : ℝ, 0 ≤ y → y ≤ 1 / 2 →
      (∑ χ ∈ F, ((Z χ).count (1 - y) T : ℝ)) ≤ B * Real.exp (A * y)) :
    (∑ χ ∈ F, ∑ i ∈ ((Z χ).heightIndices T).filter
      (fun i => 1 / 2 ≤ ((Z χ).zeros i).re),
        Real.exp (-M * (1 - ((Z χ).zeros i).re))) ≤
      2 * B ^ 2 * Real.exp (-(M * u) / 2) := by
  have hh := finite_laplace_density_bound (lowZeroIndices Z F T)
    (fun z => 1 - ((Z z.1).zeros z.2).re) A B M u hA hB hM hu
    (fun z hz => hgap z.1 (Finset.mem_sigma.mp hz).1 z.2
      (Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2).1)
    (lowZeroIndices_count_bound Z F T A B hA hB hd)
  simpa only [lowZeroIndices, Finset.sum_sigma] using hh

end Ostmann

end OAI
