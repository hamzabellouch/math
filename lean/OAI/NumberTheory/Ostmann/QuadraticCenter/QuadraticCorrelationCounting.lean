import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticCorrelationExpansion

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

theorem positiveQuadraticSum_dyadic_bound {d e S v : ℕ} [NeZero d] [NeZero e]
    (a b : ℕ → ℕ → ℂ) {R B : ℝ} (α : ℝ)
    (hS : 0 < S) (hv : 0 < v) (hR : 0 < R) (hB : 0 ≤ B)
    (hcor : ∀ w w' : ℕ,
      ‖∑ n ∈ Finset.range S,
        quadraticCrossMode d e (a (S+n)) (b (S+n)) (S+n) v w w' R α‖ ≤ B*S) :
    ‖∑ n ∈ Finset.range S,
      positiveQuadraticSum d (a (S+n)) (S+n) v R α *
        conj (positiveQuadraticSum e (b (S+n)) (S+n) v R α) / ((S+n : ℕ) : ℂ)‖ ≤ B := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
  have he' : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_neZero e
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  let W := ⌊Real.sqrt (R / ((S : ℝ)*v/d))⌋₊
  let V := ⌊Real.sqrt (R / ((S : ℝ)*v/e))⌋₊
  let P : ℝ := (v : ℝ)/(R*(Real.sqrt d*Real.sqrt e))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hW (n : ℕ) : ⌊Real.sqrt (R / (((S+n : ℕ) : ℝ)*v/d))⌋₊ ≤ W := by
    apply Nat.floor_mono
    exact quadraticCorrelation_scale_antitone hd' hS' (by exact_mod_cast Nat.le_add_right S n) hv' hR
  have hV (n : ℕ) : ⌊Real.sqrt (R / (((S+n : ℕ) : ℝ)*v/e))⌋₊ ≤ V := by
    apply Nat.floor_mono
    exact quadraticCorrelation_scale_antitone he' hS' (by exact_mod_cast Nat.le_add_right S n) hv' hR
  have hexp : (∑ n ∈ Finset.range S,
      positiveQuadraticSum d (a (S+n)) (S+n) v R α *
        conj (positiveQuadraticSum e (b (S+n)) (S+n) v R α) / ((S+n : ℕ) : ℂ)) =
      (P : ℂ) * ∑ w ∈ Finset.Ioc 0 W, ∑ w' ∈ Finset.Ioc 0 V,
        ∑ n ∈ Finset.range S,
          quadraticCrossMode d e (a (S+n)) (b (S+n)) (S+n) v w w' R α := by
    calc
      _ = ∑ n ∈ Finset.range S, (P : ℂ) *
          ∑ w ∈ Finset.Ioc 0 W, ∑ w' ∈ Finset.Ioc 0 V,
            quadraticCrossMode d e (a (S+n)) (b (S+n)) (S+n) v w w' R α := by
        apply Finset.sum_congr rfl
        intro n hn
        exact positiveQuadraticSum_cross_expansion (a (S+n)) (b (S+n)) α
          (by omega) hv hR (hW n) (hV n)
      _ = (P : ℂ) * ∑ n ∈ Finset.range S,
          ∑ w ∈ Finset.Ioc 0 W, ∑ w' ∈ Finset.Ioc 0 V,
            quadraticCrossMode d e (a (S+n)) (b (S+n)) (S+n) v w w' R α := by
        rw [Finset.mul_sum]
      _ = _ := by
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro w hw
        rw [Finset.sum_comm]
  rw [hexp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP]
  have hcount : P*((W : ℝ)*V)*S ≤ 1 :=
    quadraticCorrelation_frequency_count hd' he' hS' hv' hR
  calc
    _ ≤ P * ∑ w ∈ Finset.Ioc 0 W, ∑ w' ∈ Finset.Ioc 0 V,
        ‖∑ n ∈ Finset.range S,
          quadraticCrossMode d e (a (S+n)) (b (S+n)) (S+n) v w w' R α‖ := by
      apply mul_le_mul_of_nonneg_left _ hP
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun w hw => norm_sum_le _ _)
    _ ≤ P * ∑ _w ∈ Finset.Ioc 0 W, ∑ _w' ∈ Finset.Ioc 0 V, B*S := by
      apply mul_le_mul_of_nonneg_left _ hP
      exact Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun w' hw' => hcor w w'
    _ = (P*((W : ℝ)*V)*S)*B := by simp; ring
    _ ≤ 1*B := mul_le_mul_of_nonneg_right hcount hB
    _ = B := one_mul B

end Ostmann.QuadraticCenter

end

end OAI
