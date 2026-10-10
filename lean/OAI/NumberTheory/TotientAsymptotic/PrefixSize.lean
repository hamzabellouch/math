import OAI.NumberTheory.TotientAsymptotic.SuffixSize
import OAI.NumberTheory.TotientAsymptotic.TupleMassBound

namespace OAI

/-! Exact prefix denominators and the size bound needed for largest-prime summation. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def prefixDenominator {n : ℕ} (ζ : PrefixDatum n) : ℕ :=
  ζ.d*∏ i, (ζ.primes i-1)

lemma prefixDenominator_of_witness {x : ℝ} {H : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hL : L x H < m x) (hR : R x H < L x H) :
    prefixDenominator (prefixOfRemainder x H η) = (suffixPreimage η 0).totient := by
  rw [basic_suffix_totient_split hη hL (Nat.zero_le (R x H)) hR]
  simp only [prefixDenominator, prefixOfRemainder, ← suffixPreimage_at_R]
  simpa only [Nat.zero_add] using congrArg
    (fun n : ℕ => (suffixPreimage η (R x H)).totient*n)
    (prod_fin_shifted (R x H) (fun r => remainderPrime η r-1))

lemma basic_prefix_denominator_log_small {H : ℕ} (hPH : P H < H) (hP : 1 ≤ P H) :
    ∀ᶠ x : ℝ in atTop, ∀ ζ : PrefixDatum (R x H), IsPrefixDatum x H ζ →
      Real.log (prefixDenominator ζ : ℝ) ≤ (Real.log x)^(4/5 : ℝ) := by
  filter_upwards [basic_remainder_log_small H, m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro ζ hζ
  obtain ⟨η, hη, rfl⟩ := (isPrefixDatum_iff x H ζ).mp hζ
  have hL : L x H < m x := by unfold L; omega
  have hR : R x H < L x H := by unfold R L; omega
  rw [prefixDenominator_of_witness hη hL hR]
  have hpos := Nat.totient_pos.mpr (suffixPreimage_pos hη (i := 0))
  have hpR : (0 : ℝ) < (suffixPreimage η 0).totient := by exact_mod_cast hpos
  exact (Real.log_le_log hpR (by exact_mod_cast Nat.totient_le (suffixPreimage η 0))).trans (hx η hη)

end TotientAsymptotic

end

end OAI
