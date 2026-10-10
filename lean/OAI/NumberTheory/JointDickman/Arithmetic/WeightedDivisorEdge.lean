import OAI.NumberTheory.JointDickman.Arithmetic.DivisorEdgeReindex

namespace OAI

/-! # Transporting weighted centered labels to the additive endpoints -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- Exact transport of a weighted pair, with fixed-multiplier invariance
as its only label property. The centered label need not be multiplicative. -/
theorem weighted_divisor_edge_reindex {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {j : ℤ}
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    (N : ℕ) (w : ℕ → ℝ) (F : ℕ → ℂ)
    (hFa : ∀ n, F (a*n) = F n) (hFb : ∀ n, F (b*n) = F n)
    (hFc : ∀ n, F (c*n) = F n) :
    (∑ m ∈ divisorEdgeOld a b c N,
      w m * (star (F (a*m+1)) * F (b*m+1)).re) =
    ∑ n ∈ divisorEdgeNew a b c N j,
      w (divisorEdgeInverse a b c n) * (star (F n) * F ((n : ℤ)+j).toNat).re := by
  rw [sum_divisorEdge_reindex ha hb hc he hcop]
  apply sum_congr rfl
  intro n hn
  let m := divisorEdgeInverse a b c n
  obtain ⟨hm,hback⟩ := divisorEdge_inverse_mem ha hc he hcop hn
  obtain ⟨_,_,_,hca,hcb⟩ := mem_filter.mp hm
  have hfirst : F (a*m+1) = F n := by
    have hq : c*((a*m+1)/c) = a*m+1 := Nat.mul_div_cancel' hca
    calc
      _ = F ((a*m+1)/c) := by
        have ht := hFc ((a*m+1)/c)
        rwa [hq] at ht
      _ = F (b*((a*m+1)/c)) := (hFb _).symm
      _ = F n := by rw [hback]
  have hend : (n : ℤ)+j = ((a*((b*m+1)/c) : ℕ) : ℤ) := by
    rw [← hback]
    exact natural_divisor_edge_endpoints hc hca hcb he
  have hsecond : F (b*m+1) = F ((n : ℤ)+j).toNat := by
    have hq : c*((b*m+1)/c) = b*m+1 := Nat.mul_div_cancel' hcb
    rw [hend, Int.toNat_natCast, hFa]
    have ht := hFc ((b*m+1)/c)
    rwa [hq] at ht
  change w m * (star (F (a*m+1)) * F (b*m+1)).re = _
  rw [hfirst,hsecond]

/-- The required invariances hold for the actual moving centered labels,
simultaneously over the fixed auxiliary coefficient family. -/
theorem centered_movingBinLabel_invariant {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → ℂ) (μ : ℂ) (B : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ A ∈ (auxiliaryPrimes B).powerset, ∀ n,
      movingBinLabel J k z N ((∏ p ∈ A, p)*n)-μ = movingBinLabel J k z N n-μ := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (binLabel_auxiliary_multipliers J hJ k hk z B)] with N hN A hA n
  exact congrArg (fun v : ℂ => v-μ) (hN A hA n)

/-- The exact finite graph reindexing for the manuscript's centered bin
labels, with arbitrary real arithmetic weights. -/
theorem weighted_binLabel_edge_reindex {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → ℂ) (μ : ℂ) (B : ℕ) (w : ℕ → ℕ → ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ A ∈ (auxiliaryPrimes B).powerset,
      ∀ E ∈ (auxiliaryPrimes B).powerset, ∀ D ∈ (auxiliaryPrimes B).powerset,
      ∀ j : ℤ, ((∏ p ∈ A, p : ℕ) : ℤ)-(∏ p ∈ E, p : ℕ) = j*(∏ p ∈ D, p : ℕ) →
      (∏ p ∈ A, p).Coprime j.natAbs →
      (∑ m ∈ divisorEdgeOld (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) N,
        w N m * (star (movingBinLabel J k z N ((∏ p ∈ A, p)*m+1)-μ) *
          (movingBinLabel J k z N ((∏ p ∈ E, p)*m+1)-μ)).re) =
      ∑ n ∈ divisorEdgeNew (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) N j,
        w N (divisorEdgeInverse (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) n) *
          (star (movingBinLabel J k z N n-μ) *
            (movingBinLabel J k z N ((n : ℤ)+j).toNat-μ)).re := by
  filter_upwards [centered_movingBinLabel_invariant J hJ k hk z μ B] with N hN
  intro A hA E hE D hD j he hcop
  have hp (S : Finset ℕ) (hS : S ∈ (auxiliaryPrimes B).powerset) : 0 < ∏ p ∈ S, p :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (mem_powerset.mp hS hp)).pos)
  exact weighted_divisor_edge_reindex (hp A hA) (hp E hE) (hp D hD) he hcop N (w N)
    (fun n => movingBinLabel J k z N n-μ) (hN A hA) (hN E hE) (hN D hD)

end JointDickman

end OAI
