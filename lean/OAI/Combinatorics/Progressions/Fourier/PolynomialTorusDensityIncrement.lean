import OAI.Combinatorics.Progressions.Polynomial.PolynomialProgressionPartition
import OAI.Combinatorics.Progressions.Probability.ProgressionPartitionDensity

namespace OAI

section

namespace Erdos3

universe u

open Polynomial
open scoped NNReal BigOperators

theorem PolynomialProgressionPartitionBound.density_increment {k p : ℕ} {K : ℝ}
    (hpartition : PolynomialProgressionPartitionBound.{u} k K p)
    {ι : Type u} [Fintype ι] (P : ι → Polynomial ℝ) (hP : ∀ i, (P i).natDegree ≤ k)
    (N H : ℕ) (hH : 0 < H) (hscale : K * ((Fintype.card ι : ℝ) + 1) ≤ H)
    (hsize : H ^ (p * (Fintype.card ι + 1) ^ (2 * k)) ≤ N)
    (f : ℕ → ℝ) {F : (ι → ℝ) → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hperiod : ∀ x : ι → ℝ, ∀ m : ι → ℤ, F (fun i => x i + m i) = F x)
    (hF01 : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1) (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    {b σ : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) (hσ : 0 < σ)
    (hsmall : 4 * (k : ℝ) * L ≤ σ * H)
    (hscore : σ ≤ 𝔼 n : Fin N, (f n.val - b) * F (fun i => (P i).eval (n.val : ℝ))) :
    ∃ q a len : ℕ, 0 < q ∧ σ * H / (2 : ℝ) ^ (k + 2) ≤ len ∧
      (∀ n < len, a + q * n < N) ∧ b < 𝔼 n : Fin len, f (a + q * n.val) := by
  have hN : 0 < N := (pow_pos hH _).trans_le hsize
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  obtain ⟨Q, c, hcard, hc, herror⟩ := hpartition ι P hP N H hH hscale hsize F L hF hperiod hF01
  have hcount : (Fintype.card Q.Label : ℝ) * H ≤ (2 : ℝ) ^ k * N := by exact_mod_cast hcard
  have hsmall' : 4 * ((k : ℝ) * L / H) ≤ σ := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hHR).mpr (by nlinarith)
  obtain ⟨q, a, len, hq, hlarge, hinside, hdense⟩ := Q.density_increment hN hH f
    (fun n => F (fun i => (P i).eval (n : ℝ))) c hb hσ (by positivity : 0 < (2 : ℝ) ^ k)
    hf (fun n _ => hF01 _) (fun i => (hc i).1) (by positivity) hsmall' hcount herror hscore
  refine ⟨q, a, len, hq, ?_, hinside, hdense⟩
  have heq : (2 : ℝ) ^ (k + 2) = 4 * (2 : ℝ) ^ k := by rw [pow_add]; ring
  simpa only [heq] using hlarge

theorem polynomial_torus_density_increment (k : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧
      ∀ (ι : Type u) [Fintype ι] (P : ι → Polynomial ℝ),
        (∀ i, (P i).natDegree ≤ k) → ∀ (N H : ℕ), 0 < H →
        K * ((Fintype.card ι : ℝ) + 1) ≤ H →
        H ^ (p * (Fintype.card ι + 1) ^ (2 * k)) ≤ N →
        ∀ (f : ℕ → ℝ) (F : (ι → ℝ) → ℝ) (L : ℝ≥0), LipschitzWith L F →
        (∀ x : ι → ℝ, ∀ m : ι → ℤ, F (fun i => x i + m i) = F x) →
        (∀ x, F x ∈ Set.Icc (0 : ℝ) 1) → (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) →
        ∀ b σ : ℝ, b ∈ Set.Icc (0 : ℝ) 1 → 0 < σ → 4 * (k : ℝ) * L ≤ σ * H →
        σ ≤ (𝔼 n : Fin N, (f n.val - b) * F (fun i => (P i).eval (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ σ * H / (2 : ℝ) ^ (k + 2) ≤ len ∧
          (∀ n < len, a + q * n < N) ∧ b < 𝔼 n : Fin len, f (a + q * n.val) := by
  obtain ⟨K, p, hK, hp, hpartition⟩ := exists_polynomial_progression_partition_bound.{u} k
  refine ⟨K, p, hK, hp, ?_⟩
  intro ι _ P hP N H hH hscale hsize f F L hF hperiod hF01 hf b σ hb hσ hsmall hscore
  exact hpartition.density_increment P hP N H hH hscale hsize f hF hperiod hF01 hf hb hσ hsmall hscore

end Erdos3

end

end OAI
