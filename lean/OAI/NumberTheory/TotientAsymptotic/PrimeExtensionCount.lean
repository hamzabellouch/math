import OAI.NumberTheory.TotientAsymptotic.QuarterPrimeCount

namespace OAI

/-! Distinct totient values after adjoining a large prime to a residual preimage. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def quarterPrimes (x : ℝ) (d : ℕ) : Finset ℕ :=
  (Nat.primesLE ⌊1+x/d⌋₊).filter (fun p => x^(1/4:ℝ) ≤ p ∧ ((p-1)*d:ℕ) ≤ x)

def primeExtensionValues (x : ℝ) (d : ℕ) : Finset ℕ :=
  (quarterPrimes x d).biUnion (fun p => {(p-1)*d,p*d})

lemma mem_quarterPrimes {x : ℝ} {d p : ℕ} (hd : 0 < d) :
    p ∈ quarterPrimes x d ↔ p.Prime ∧ x^(1/4:ℝ) ≤ p ∧ ((p-1)*d:ℕ) ≤ x := by
  classical
  constructor
  · intro hp
    obtain ⟨hp,hx,hs⟩ := Finset.mem_filter.mp hp
    exact ⟨(Nat.mem_primesLE.mp hp).2,hx,hs⟩
  · rintro ⟨hp,hx,hs⟩
    refine Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor ?_,hp⟩,hx,hs⟩
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    have hpn : 1 ≤ p := hp.one_le
    have hle : ((p:ℝ)-1)*d ≤ x := by exact_mod_cast hs
    have hh := (le_div_iff₀ hdR).mpr hle
    linarith

lemma prime_extension_values_card (x : ℝ) (d : ℕ) :
    (primeExtensionValues x d).card ≤ 2*(quarterPrimes x d).card := by
  classical
  calc
    _ ≤ ∑ _p ∈ quarterPrimes x d,({(0:ℕ),1}:Finset ℕ).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun p _ => by simp; exact Finset.card_insert_le _ _))
    _ = _ := by simp; omega

theorem prime_extension_count_upper : ∀ᶠ x : ℝ in atTop,
    ∀ R : Finset ℕ,(∀ d ∈ R,0 < d) →
    ((R.biUnion (primeExtensionValues x)).card:ℝ) ≤
      (64*x/Real.log x)*(∑ d ∈ R,(d:ℝ)⁻¹) := by
  classical
  filter_upwards [quarter_prime_count_upper,eventually_gt_atTop (1:ℝ)] with x hx hx1
  intro R hR
  have hcount (d : ℕ) (hd : d ∈ R) :
      ((primeExtensionValues x d).card:ℝ) ≤ 64*x/(d*Real.log x) := by
    have hh := hx d (hR d hd) (quarterPrimes x d) (fun p hp => (mem_quarterPrimes (hR d hd)).mp hp)
    have hc : ((primeExtensionValues x d).card:ℝ) ≤ 2*(quarterPrimes x d).card :=
      by exact_mod_cast prime_extension_values_card x d
    calc
      _ ≤ 2*((quarterPrimes x d).card:ℝ) := hc
      _ ≤ 2*(32*x/(d*Real.log x)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ ∑ d ∈ R,((primeExtensionValues x d).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (R.biUnion (primeExtensionValues x)).card ≤
        ∑ d ∈ R,(primeExtensionValues x d).card)
    _ ≤ ∑ d ∈ R,64*x/(d*Real.log x) := Finset.sum_le_sum hcount
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring

end TotientAsymptotic

end

end OAI
