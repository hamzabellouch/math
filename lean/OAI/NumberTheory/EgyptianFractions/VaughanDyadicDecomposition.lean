import OAI.NumberTheory.EgyptianFractions.VaughanDyadic
import OAI.NumberTheory.EgyptianFractions.VaughanDecomposition
import OAI.NumberTheory.EgyptianFractions.DivisorSquareMean

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Finset

namespace Problem337.Vaughan

lemma long_hyperbola_eq_filtered_product (N U V : ℕ) :
    (hyperbola N).filter (fun d => U < d.1 ∧ V < d.2) =
      (Ioc U N ×ˢ Ioc V N).filter (fun d => d.1 * d.2 ≤ N) := by
  ext d
  rcases d with ⟨a, b⟩
  simp only [mem_filter, mem_hyperbola, mem_product, mem_Ioc]
  constructor
  · rintro ⟨⟨ha, hb, hp⟩, hU, hV⟩
    exact ⟨⟨⟨hU, (Nat.le_mul_of_pos_right a hb).trans hp⟩,
      ⟨hV, (Nat.le_mul_of_pos_left b ha).trans hp⟩⟩, hp⟩
  · rintro ⟨⟨⟨hU, ha⟩, ⟨hV, hb⟩⟩, hp⟩
    exact ⟨⟨by omega, by omega, hp⟩, hU, hV⟩

/-- The dyadic block with the actual arithmetic coefficients in Vaughan's identity. -/
def typeIIBlock (N U V j : ℕ) (w : ℕ → ℂ) : ℂ :=
  VaughanDyadic.block N U V j
    (fun m n => (typeIICoefficient U m : ℂ) * (Λ n : ℂ) * w (m * n))

/-- No arithmetic coefficient or hyperbolic cutoff is lost in dyadic decomposition. -/
theorem typeII_eq_sum_dyadic_blocks (N U V : ℕ) (w : ℕ → ℂ) :
    weightedSum (Ioc 0 N) w (typeIICoefficient U * longPart V Λ) =
      ∑ j ∈ range (Nat.log 2 N + 1), typeIIBlock N U V j w := by
  rw [typeII_eq_hyperbola, long_hyperbola_eq_filtered_product]
  exact VaughanDyadic.sum_filtered_product_eq_sum_blocks (E := ℂ) N U V
    (fun m n => (typeIICoefficient U m : ℂ) * (Λ n : ℂ) * w (m * n))

theorem norm_typeII_le_sum_dyadic_blocks (N U V : ℕ) (w : ℕ → ℂ) :
    ‖weightedSum (Ioc 0 N) w (typeIICoefficient U * longPart V Λ)‖ ≤
      ∑ j ∈ range (Nat.log 2 N + 1), ‖typeIIBlock N U V j w‖ := by
  rw [typeII_eq_sum_dyadic_blocks]
  exact norm_sum_le _ _

/-- A genuine uniform block bound has only a logarithmic decomposition cost. -/
theorem norm_typeII_le_dyadic_log_budget (N U V : ℕ) (w : ℕ → ℂ)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ j < Nat.log 2 N + 1, ‖typeIIBlock N U V j w‖ ≤ B) :
    ‖weightedSum (Ioc 0 N) w (typeIICoefficient U * longPart V Λ)‖ ≤
      (1 + Real.log N / Real.log 2) * B := by
  let F : ℕ → ℕ → ℂ :=
    fun m n => (typeIICoefficient U m : ℂ) * (Λ n : ℂ) * w (m * n)
  have he : weightedSum (Ioc 0 N) w (typeIICoefficient U * longPart V Λ) =
      ∑ m ∈ Ioc U N, ∑ n ∈ Ioc V (N / m), F m n := by
    rw [typeII_eq_sum_dyadic_blocks, VaughanDyadic.sum_hyperbola_eq_sum_blocks]
    rfl
  rw [he]
  exact VaughanDyadic.norm_hyperbola_le_log_budget N U V F B hB0 hB

/-- The complete finite Vaughan envelope, with its Type II term split into
actual dyadic blocks ready for interval correlation estimates. -/
theorem norm_vonMangoldt_sum_le_dyadic (N U V : ℕ) (w : ℕ → ℂ) (B₁ B₂ : ℕ → ℝ)
    (hw : ∀ n ∈ Ioc 0 N, ‖w n‖ ≤ 1)
    (hfirst : ∀ a ∈ Ioc 0 (min U N), ∀ k ≤ N / a,
      ‖∑ b ∈ Ioc 0 k, w (a * b)‖ ≤ B₁ a)
    (hsecond : ∀ a ∈ Ioc 0 (min (U * V) N),
      ‖∑ b ∈ Ioc 0 (N / a), w (a * b)‖ ≤ B₂ a) :
    ‖weightedSum (Ioc 0 N) w Λ‖ ≤
      (V : ℝ) * Real.log V +
      2 * Real.log N * (∑ a ∈ Ioc 0 (min U N), B₁ a) +
      Real.log N * (∑ a ∈ Ioc 0 (min (U * V) N), B₂ a) +
      ∑ j ∈ range (Nat.log 2 N + 1), ‖typeIIBlock N U V j w‖ := by
  have h := norm_vonMangoldt_sum_le N U V w B₁ B₂ hw hfirst hsecond
  rw [← typeII_eq_hyperbola] at h
  exact h.trans (add_le_add le_rfl (norm_typeII_le_sum_dyadic_blocks N U V w))

/-- Sharp unconditional row energy for the actual Type II coefficient in a dyadic shell. -/
theorem typeII_shell_energy_le (N U j : ℕ) :
    (∑ m ∈ VaughanDyadic.shell U N j, ‖(typeIICoefficient U m : ℂ)‖ ^ 2) ≤
      (2 ^ (j + 1) : ℕ) * (1 + Real.log (2 ^ (j + 1) : ℕ)) ^ 3 := by
  have hT : VaughanDyadic.shell U N j ⊆ Ioc 0 (2 ^ (j + 1)) := by
    intro m hm
    have h := VaughanDyadic.mem_shell.mp hm
    exact mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le U) h.1, h.2.2.2.le⟩
  have h := DivisorSquareMean.sum_norm_sq_le_log_of_subset
    (fun m => (typeIICoefficient U m : ℂ)) (VaughanDyadic.shell U N j)
    (2 ^ (j + 1)) 1 hT (by
      intro m hm
      simpa only [Complex.norm_real, Real.norm_eq_abs, one_mul] using
        abs_typeIICoefficient_le_divisors_card U m)
  simpa only [one_pow, one_mul] using h

end Problem337.Vaughan

end

end OAI
