import OAI.NumberTheory.JointDickman.Counting.PositiveLagMass

namespace OAI

/-! # Reversing a coefficient representation reverses its lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

def graphTripleSwap (i : GraphCoefficientTriple) : GraphCoefficientTriple :=
  (i.1,i.2.2,i.2.1)

theorem graphTripleSwap_involutive : Function.Involutive graphTripleSwap := fun _ => rfl

theorem divisor_lag_coprime_swap {a b c : ℕ} {j : ℤ}
    (he : (a : ℤ)-b = j*c) (ha : a.Coprime j.natAbs) : b.Coprime j.natAbs := by
  apply Nat.coprime_of_dvd'
  intro p _ hpb hpj
  have hpj' : (p : ℤ) ∣ j := Int.natCast_dvd.mpr hpj
  have hpb' : (p : ℤ) ∣ (b : ℤ) := by exact_mod_cast hpb
  have hd := dvd_add hpb' (dvd_mul_of_dvd_left hpj' (c : ℤ))
  have hpa' : (p : ℤ) ∣ (a : ℤ) := by
    have hae : (a : ℤ) = b+j*c := by linarith
    rwa [← hae] at hd
  have hpa : p ∣ a := by exact_mod_cast hpa'
  exact Nat.dvd_one.mpr (Nat.eq_one_of_dvd_coprimes ha hpa hpj)

theorem graphTripleSwap_lag {B T : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) :
    graphTripleLag (graphTripleSwap i) = -graphTripleLag i := by
  classical
  have hs := graphTriple_subsets hi
  have hc : (∏ p ∈ i.1, p : ℕ) ≠ 0 := prod_ne_zero_iff.mpr
    (fun p hp => (auxiliaryPrimes_prime B p (hs.1 hp)).ne_zero)
  have he := (mem_filter.mp hi).2.2.2.2.1
  change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
    graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at he
  have hflip : ((∏ p ∈ i.2.2, p : ℕ) : ℤ)-(∏ p ∈ i.2.1, p : ℕ) =
      (-graphTripleLag i)*(∏ p ∈ i.1, p : ℕ) := by linarith
  change (((∏ p ∈ i.2.2, p : ℕ) : ℤ)-(∏ p ∈ i.2.1, p : ℕ)) /
      (∏ p ∈ i.1, p : ℕ) = -graphTripleLag i
  rw [hflip, Int.mul_ediv_cancel _ (by exact_mod_cast hc)]

theorem graphTripleSwap_mem {B T : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) : graphTripleSwap i ∈ arithmeticGraphTriples B T := by
  classical
  have hs := graphTriple_subsets hi
  have hg := (mem_filter.mp hi).2
  have hlag := graphTripleSwap_lag hi
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_powerset.mpr hs.1,
    mem_product.mpr ⟨mem_powerset.mpr hs.2.2,mem_powerset.mpr hs.2.1⟩⟩,?_⟩
  change i.2.2 ≠ i.2.1 ∧ graphTripleLag (graphTripleSwap i) ≠ 0 ∧
    (graphTripleLag (graphTripleSwap i)).natAbs < T ∧
    ((∏ p ∈ i.2.2, p : ℕ) : ℤ)-(∏ p ∈ i.2.1, p : ℕ) =
      graphTripleLag (graphTripleSwap i)*(∏ p ∈ i.1, p : ℕ) ∧
    (∏ p ∈ i.2.2, p).Coprime (graphTripleLag (graphTripleSwap i)).natAbs
  rw [hlag, Int.natAbs_neg, neg_ne_zero]
  refine ⟨Ne.symm hg.1,hg.2.1,hg.2.2.1,?_,?_⟩
  · have he := hg.2.2.2.1
    change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
      graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at he
    linarith
  · exact divisor_lag_coprime_swap hg.2.2.2.1 hg.2.2.2.2

theorem graphTripleSwap_supported {B T : ℕ} {i : GraphCoefficientTriple} {j : ℤ}
    (hi : i ∈ supportedGraphTriples B T j) :
    graphTripleSwap i ∈ supportedGraphTriples B T (-j) := by
  classical
  have h := mem_filter.mp hi
  apply mem_filter.mpr
  refine ⟨graphTripleSwap_mem h.1,?_,h.2.2.2,h.2.2.1⟩
  rw [graphTripleSwap_lag h.1,h.2.1]

theorem graphTriple_harmonic_neg (B T : ℕ) (j : ℤ) :
    (∑ i ∈ supportedGraphTriples B T (-j),
      (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
        coefficientWeight B (∏ p ∈ i.2.2, p)) /
          (((∏ p ∈ i.2.1, p : ℕ) : ℝ)*(∏ p ∈ i.2.2, p : ℕ))) =
    (∑ i ∈ supportedGraphTriples B T j,
      (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
        coefficientWeight B (∏ p ∈ i.2.2, p)) /
          (((∏ p ∈ i.2.1, p : ℕ) : ℝ)*(∏ p ∈ i.2.2, p : ℕ))) := by
  classical
  apply sum_bij (fun i _ => graphTripleSwap i)
  · intro i hi
    simpa only [neg_neg] using graphTripleSwap_supported hi
  · intro i _ k _ hik
    exact graphTripleSwap_involutive.injective hik
  · intro i hi
    exact ⟨graphTripleSwap i,graphTripleSwap_supported hi,graphTripleSwap_involutive i⟩
  · intro i _
    simp only [graphTripleSwap]
    ring

end JointDickman

end OAI
