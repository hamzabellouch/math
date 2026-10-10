import OAI.NumberTheory.Ostmann.ZeroDensity.SparsePrincipalCoefficients
import OAI.NumberTheory.Ostmann.Supply.BilinearCube

namespace OAI

/-! # A uniform coefficient bound for the truncated sparse weight -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def sparsePatternMellin {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (t : ℝ) (χ : MulChar (ZMod p) ℂ) : Bool × Bool → ℂ
  | (false, false) => if χ = 1 then 1 else 0
  | (true, false) => mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x) χ
  | (false, true) => mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x) χ
  | (true, true) => mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ 2) χ

theorem sparsePatternMellin_norm_sum {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (hsym : ∀ b, -b ∈ E ↔ b ∈ E)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hp : (36 : ℝ) ≤ p)
    (χ : MulChar (ZMod p) ℂ) :
    (∑ b : Bool × Bool, ‖sparsePatternMellin E t χ b‖) ≤ 1 + 6 / p := by
  have hp0 : (0 : ℝ) < p := by linarith
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, sparsePatternMellin]
  by_cases hχ : χ = 1
  · subst χ
    have h₁ := sparse_principal_coefficients_le E hE hsym t ht ht1 1 (Or.inl rfl)
    have h₂ := sparse_principal_coefficients_le E hE hsym t ht ht1 2 (Or.inr rfl)
    simp only [pow_one] at h₁
    simp only [ite_true, norm_one]
    ring_nf at h₁ h₂ ⊢
    linarith
  · have h₁ := sparse_power_mellin_le E t ht ht1 1 (Or.inl rfl) χ
    have h₂ := sparse_power_mellin_le E t ht ht1 2 (Or.inr rfl) χ
    simp only [pow_one] at h₁
    simp only [hχ, ite_false, norm_zero]
    have hs : 6 ≤ Real.sqrt (p : ℝ) := (Real.le_sqrt (by norm_num) hp0.le).mpr (by nlinarith)
    have hs0 : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
    have hh : 6 / Real.sqrt (p : ℝ) ≤ 1 := (div_le_one hs0).mpr hs
    have hh' : 0 ≤ 6 / (p : ℝ) := by positivity
    ring_nf at h₁ h₂ hh hh' ⊢
    linarith

noncomputable def sparseTruncatedMellinCoefficient {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] (E : ∀ i, Finset (ZMod (p i)))
    (t : ℝ) (K : ℕ) (χ : ∀ i, MulChar (ZMod (p i)) ℂ) : ℂ :=
  ∑ v ∈ (Finset.univ : Finset (BilinearCube n)).filter
    (fun v => cubeDegree v false ≤ K ∧ cubeDegree v true ≤ K),
      ∏ i, sparsePatternMellin (E i) t (χ i) (v i)

/-- The norm of each full multiplicative coefficient is at most exp(6H),
independently of the truncation order and of the number of primes. -/
theorem sparseTruncatedMellinCoefficient_norm_le {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] (E : ∀ i, Finset (ZMod (p i)))
    (hE : ∀ i, 0 ∉ E i) (hsym : ∀ i b, -b ∈ E i ↔ b ∈ E i)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hp : ∀ i, (36 : ℝ) ≤ p i)
    (K : ℕ) (χ : ∀ i, MulChar (ZMod (p i)) ℂ) :
    ‖sparseTruncatedMellinCoefficient p E t K χ‖ ≤
      Real.exp (6 * ∑ i, (p i : ℝ)⁻¹) := by
  unfold sparseTruncatedMellinCoefficient
  calc
    _ ≤ ∑ v ∈ (Finset.univ : Finset (BilinearCube n)).filter
        (fun v => cubeDegree v false ≤ K ∧ cubeDegree v true ≤ K),
        ∏ i, ‖sparsePatternMellin (E i) t (χ i) (v i)‖ := by
      simpa only [norm_prod] using norm_sum_le
        ((Finset.univ : Finset (BilinearCube n)).filter
          (fun v => cubeDegree v false ≤ K ∧ cubeDegree v true ≤ K))
        (fun v => ∏ i, sparsePatternMellin (E i) t (χ i) (v i))
    _ ≤ ∑ v : BilinearCube n, ∏ i, ‖sparsePatternMellin (E i) t (χ i) (v i)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    _ = ∏ i, ∑ b : Bool × Bool, ‖sparsePatternMellin (E i) t (χ i) b‖ :=
      (Fintype.prod_sum (fun (i : Fin n) (b : Bool × Bool) =>
        ‖sparsePatternMellin (E i) t (χ i) b‖)).symm
    _ ≤ ∏ i, (1 + 6 / (p i : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      · intro i _
        exact sparsePatternMellin_norm_sum (E i) (hE i) (hsym i) t ht ht1 (hp i) (χ i)
    _ ≤ ∏ i, Real.exp (6 / (p i : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro i _
        positivity
      · intro i _
        linarith [Real.add_one_le_exp (6 / (p i : ℝ))]
    _ = _ := by rw [← Real.exp_sum]; simp only [div_eq_mul_inv, ← Finset.mul_sum]

end Ostmann

end OAI
