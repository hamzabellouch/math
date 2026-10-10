import OAI.NumberTheory.TotientAsymptotic.TupleTotients

namespace OAI

/-! Exact prime-prefix factorization and minimization over a common inverse fiber. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def tuplePrimeProduct {r : ℕ} (τ : TotientTuple r) : ℕ := ∏ i, tuplePrimes τ i

def tupleLeastCandidate {r : ℕ} (τ : TotientTuple r) : ℕ :=
  tuplePrimeProduct τ * ell τ.tail.d

lemma wholePreimage_prefix_split {x : ℝ} {H : ℕ} (p : ℕ)
    (η : RemainderDatum (L x H)) (hRL : R x H ≤ L x H) :
    wholePreimage p η = tuplePrimeProduct (witnessTuple p η)*remainderTail x H η := by
  unfold tuplePrimeProduct tuplePrimes witnessTuple
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,prefixOfRemainder]
  rw [prod_fin_shifted]
  unfold wholePreimage suffixPreimage remainderTail
  rw [prod_Icc_split_at (Nat.zero_le (R x H)) hRL]
  simp only [Nat.zero_add]
  ring

lemma tuplePrimeProduct_pos {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : IsBasicTuple x H t τ) : 0 < tuplePrimeProduct τ := by
  exact Finset.prod_pos (fun i _ => (basic_tuple_primes hPH hτ i).pos)

/-- If every inverse image has a fixed multiplicative prefix, minimizing the
remaining inverse image minimizes the whole fiber. -/
lemma ell_of_common_prefix {v d b : ℕ} (hv : IsTotient v) (hd : IsTotient d)
    (hb : 0 < b) (hreal : (b*ell d).totient=v)
    (hcommon : ∀ n : ℕ, 0 < n → n.totient=v →
      ∃ w : ℕ, 0 < w ∧ w.totient=d ∧ n=b*w) :
    ell v=b*ell d := by
  apply le_antisymm (ell_le (Nat.mul_pos hb (ell_spec hd).1) hreal)
  obtain ⟨w,hw,hwd,he⟩ := hcommon (ell v) (ell_spec hv).1 (ell_spec hv).2
  rw [he]
  exact Nat.mul_le_mul_left b (ell_le hw hwd)

lemma coprime_of_prime_gt {p w : ℕ} (hp : p.Prime) (hw : 0 < w) (hwp : w < p) :
    p.Coprime w := by
  apply hp.coprime_iff_not_dvd.mpr
  intro h
  exact (not_le_of_gt hwp) (Nat.le_of_dvd hw h)

/-- Replacing the tail of a represented value by its least preimage preserves
that value once the tail is smaller than every prefix prime. -/
lemma tuple_candidate_realizes {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : IsBasicTuple x H t τ)
    {w : ℕ} (hw : 0 < w) (hwd : w.totient=τ.tail.d)
    (hsmall : ∀ i, w < tuplePrimes τ i)
    (hreal : (tuplePrimeProduct τ*w).totient=tupleValue τ) :
    (tupleLeastCandidate τ).totient=tupleValue τ := by
  have hd : IsTotient τ.tail.d := ⟨w,hw,hwd⟩
  have he := ell_le hw hwd
  have hc : (tuplePrimeProduct τ).Coprime w := Nat.coprime_prod_left_iff.mpr
    (fun i _ => coprime_of_prime_gt (basic_tuple_primes hPH hτ i) hw (hsmall i))
  have hce : (tuplePrimeProduct τ).Coprime (ell τ.tail.d) := Nat.coprime_prod_left_iff.mpr
    (fun i _ => coprime_of_prime_gt (basic_tuple_primes hPH hτ i) (ell_spec hd).1
      (he.trans_lt (hsmall i)))
  unfold tupleLeastCandidate
  rw [Nat.totient_mul hce,(ell_spec hd).2]
  rwa [Nat.totient_mul hc,hwd] at hreal

end TotientAsymptotic

end

end OAI
