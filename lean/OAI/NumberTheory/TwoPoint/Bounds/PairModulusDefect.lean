import OAI.NumberTheory.TwoPoint.Bounds.PairPrimeCosts
import OAI.NumberTheory.TwoPoint.Bounds.MultiplicativePrimeProducts

namespace OAI

/-! The mean modulus loss is controlled by the separate tuple and padding
prime-defect moments. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma squarefree_pair_defect {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1) (hf : OneBounded f) (hg : OneBounded g)
    {n : ℕ} (hn : Squarefree n) :
    1 - ‖f n * g n‖ ≤ ∑ p ∈ n.primeFactors, (1 - ‖f p * g p‖) := by
  have he := multiplicative_prime_product_defect hfm hgm hf1 hg1 hf hg n.primeFactors
    (fun _ hp => Nat.prime_of_mem_primeFactors hp)
  rwa [Nat.prod_primeFactors_of_squarefree hn] at he

lemma tuple_padding_modulus_defect {J : ℕ} {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1) (hf : OneBounded f) (hg : OneBounded g)
    (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint (primeTuplePool P) Q)
    (W : ℝ) (hW : 0 < W) (hmass : ∀ j, W ≤ primeHarmonicMass (P j)) :
    (∑ d ∈ primeTupleDivisors P, ∑ q ∈ retainedPrimeDivisors Q,
      (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) * (1 - ‖f (d * q) * g (d * q)‖)) ≤
      paddingTiltNormalizer Q * (∏ j, primeHarmonicMass (P j)) *
        ((∑ p ∈ primeTuplePool P, (1 - ‖f p * g p‖) / (p : ℝ)) / W +
          ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * (1 - ‖f p * g p‖)) := by
  apply le_trans _ (tuple_padding_prime_cost_bound P Q hprime hdisjoint hQ hPQ
    (fun p => 1 - ‖f p * g p‖) (fun p hp => by
      have hpp := primeTuplePool_prime hprime hp
      rw [norm_mul]
      exact sub_nonneg.mpr ((mul_le_mul (hf p hpp.pos) (hg p hpp.pos)
        (norm_nonneg _) zero_le_one).trans (by norm_num))) W hW hmass)
  apply sum_le_sum
  intro d hd
  apply sum_le_sum
  intro q hq
  have hsq : Squarefree (d * q) := (Nat.squarefree_mul
    (tuple_padding_coprime P Q hprime hdisjoint hQ hPQ hd hq)).mpr
      ⟨(primeTupleDivisors_arithmetic P hprime hdisjoint hd).1,
        retainedPrimeDivisor_squarefree Q hQ hq⟩
  exact mul_le_mul_of_nonneg_left (squarefree_pair_defect hfm hgm hf1 hg1 hf hg hsq)
    (by positivity)

lemma padding_modulus_defect_cost_le {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g)
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    (∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * (1 - ‖f p * g p‖)) ≤
      4 * ∑ p ∈ Q, (1 - ‖f p * g p‖) / (p : ℝ) := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).pos
  have hd : 0 ≤ 1 - ‖f p * g p‖ := by
    rw [norm_mul]
    exact sub_nonneg.mpr ((mul_le_mul (hf p (hQ p hp).pos) (hg p (hQ p hp).pos)
      (norm_nonneg _) zero_le_one).trans (by norm_num))
  calc
    _ ≤ (4 / (p : ℝ)) * (1 - ‖f p * g p‖) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) hpR (by linarith)) hd
    _ = _ := by ring

end TwoPointCorrelations

end OAI
