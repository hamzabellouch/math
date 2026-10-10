import OAI.NumberTheory.Ostmann.HybridSieve.PacketBound

namespace OAI

open MeasureTheory FourierTransform
open scoped FourierTransform Real
namespace Ostmann.HybridSieve

lemma packetFamily_integral_bound {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (a : κ → ℂ) (v : ι → κ → ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (freq : κ → ℝ) (f : SchwartzMap ℝ ℂ)
    (c K : ℝ) (hc : 0 ≤ c)
    (hf : ∀ t : ℝ, |t| ≤ 1 → c ≤ ‖𝓕 f t‖)
    (hspatial : ∀ x : ℝ,
      (∑ i, w i * ‖∑ n ∈ s, a n * v i n * f (x-freq n)‖^2) ≤
        K * ∑ n ∈ s, ‖a n‖^2 * ‖f (x-freq n)‖^2) :
    c^2 * (∑ i, w i * (∫ t in Set.Icc (-1:ℝ) 1,
      ‖∑ n ∈ s, a n * v i n * fourierPhase (freq n) t‖^2)) ≤
        K * (∫ x : ℝ, ‖f x‖^2) * ∑ n ∈ s, ‖a n‖^2 := by
  let P (i : ι) := fourierPacket s (fun n => a n*v i n) freq f
  have hp (i : ι) : Integrable (fun x : ℝ => ‖∑ n ∈ s, a n*v i n*f (x-freq n)‖^2) := by
    simpa only [P, fourierPacket_apply] using
      (SchwartzMap.memLp (P i) 2).integrable_norm_pow (by norm_num)
  have htrans (n : κ) : Integrable (fun x : ℝ => ‖f (x-freq n)‖^2) := by
    simpa only [SchwartzMap.compSubConstCLM_apply] using
      (SchwartzMap.memLp (f.compSubConstCLM ℂ (freq n)) 2).integrable_norm_pow (by norm_num)
  have hright : Integrable (fun x : ℝ =>
      K * ∑ n ∈ s, ‖a n‖^2 * ‖f (x-freq n)‖^2) := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ (fun n _ => (htrans n).const_mul _)
  calc
    _ = ∑ i, w i * (c^2 * (∫ t in Set.Icc (-1:ℝ) 1,
        ‖∑ n ∈ s, a n*v i n*fourierPhase (freq n) t‖^2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, w i * (∫ x : ℝ, ‖∑ n ∈ s, a n*v i n*f (x-freq n)‖^2) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (packet_integral_bound s (fun n => a n*v i n) freq f c hc hf) (hw i)
    _ = ∫ x : ℝ, ∑ i, w i * ‖∑ n ∈ s, a n*v i n*f (x-freq n)‖^2 := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul]
      · intro i _
        exact (hp i).const_mul _
    _ ≤ ∫ x : ℝ, K * ∑ n ∈ s, ‖a n‖^2 * ‖f (x-freq n)‖^2 := by
      apply integral_mono _ hright hspatial
      exact integrable_finsetSum _ (fun i _ => (hp i).const_mul _)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum]
      · have ht (n : κ) : (∫ x : ℝ, ‖f (x-freq n)‖^2) = ∫ x : ℝ, ‖f x‖^2 := by
          exact integral_sub_right_eq_self (fun x : ℝ => ‖f x‖^2) (freq n)
        simp_rw [integral_const_mul, ht]
        rw [← Finset.sum_mul]
        ring
      · intro n _
        exact (htrans n).const_mul _

end Ostmann.HybridSieve

end OAI
