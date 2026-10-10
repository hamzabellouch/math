import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticCorrelationCounting

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

theorem positiveQuadraticSum_mul_amplitude (d : ℕ) (a : ℕ → ℂ) (c : ℂ)
    (s v : ℕ) (R α : ℝ) :
    positiveQuadraticSum d (fun w => c * a w) s v R α = c * positiveQuadraticSum d a s v R α := by
  unfold positiveQuadraticSum normalizedSmoothQuadraticSum
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

theorem quadraticCrossMode_mul_amplitude (d e : ℕ) (a b : ℕ → ℂ) (c : ℂ)
    (s v w w' : ℕ) (R α : ℝ) :
    quadraticCrossMode d e (fun w => c * a w) b s v w w' R α =
      c * quadraticCrossMode d e a b s v w w' R α := by
  unfold quadraticCrossMode
  ring

theorem positiveQuadraticSum_weighted_dyadic_bound {d e S v : ℕ} [NeZero d] [NeZero e]
    (a b : ℕ → ℕ → ℂ) (weight : ℕ → ℂ) {R B : ℝ} (α : ℝ)
    (hS : 0 < S) (hv : 0 < v) (hR : 0 < R) (hB : 0 ≤ B)
    (hcor : ∀ w w' : ℕ,
      ‖∑ n ∈ Finset.range S, weight (S+n) *
        quadraticCrossMode d e (a (S+n)) (b (S+n)) (S+n) v w w' R α‖ ≤ B*S) :
    ‖∑ n ∈ Finset.range S, weight (S+n) *
      (positiveQuadraticSum d (a (S+n)) (S+n) v R α *
        conj (positiveQuadraticSum e (b (S+n)) (S+n) v R α) / ((S+n : ℕ) : ℂ))‖ ≤ B := by
  have hh := positiveQuadraticSum_dyadic_bound (d := d) (e := e) (S := S) (v := v) (R := R) (B := B)
    (fun s w => weight s * a s w) b α hS hv hR hB (fun w w' => ?_)
  · simpa only [positiveQuadraticSum_mul_amplitude, mul_assoc, mul_div_assoc] using hh
  · simpa only [quadraticCrossMode_mul_amplitude] using hcor w w'

theorem sum_range_dyadic_indicator {A : Type*} [AddCommMonoid A]
    (S : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.Ico S (2*S)) (f : ℕ → A) :
    (∑ n ∈ Finset.range S, if S+n ∈ T then f (S+n) else 0) = ∑ s ∈ T, f s := by
  have heq : (Finset.Ico S (2*S)).filter (fun s => s ∈ T) = T := by
    ext s
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hT h, h⟩⟩
  calc
    _ = ∑ s ∈ Finset.Ico S (2*S), if s ∈ T then f s else 0 := by
      rw [Finset.sum_Ico_eq_sum_range, show 2*S-S = S by omega]
    _ = _ := by rw [← Finset.sum_filter, heq]

end Ostmann.QuadraticCenter

end

end OAI
