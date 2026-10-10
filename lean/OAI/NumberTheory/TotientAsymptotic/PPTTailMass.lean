import OAI.NumberTheory.TotientAsymptotic.PrimeGrid
import OAI.NumberTheory.TotientAsymptotic.CofactorMass

namespace OAI

/-!
Finite reciprocal-totient sums for the common factor and the fixed small
tail in the PPT comparison argument.  A chosen prime list recovers the
integer itself, so its reciprocal totient is counted with its full integer
multiplicity.  No injectivity of the totient function is needed.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

private lemma ppt_prime_pi_mass {N : ℕ} (T : Fin N → Finset ℕ) :
    (∑ p ∈ Fintype.piFinset T, reciprocalShiftWeight p) =
      ∏ j, ∑ q ∈ T j, ((q-1 : ℕ) : ℝ)⁻¹ := by
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [reciprocalShiftWeight, Nat.cast_prod, Finset.prod_inv_distrib]

/-- A finite family of products of `h` primes has mass at most the `h`th
power of the available reciprocal shifted-prime mass. -/
theorem ppt_fixed_length_tail_mass {h : ℕ} (S T : Finset ℕ)
    (p : ℕ → Fin h → ℕ)
    (hprime : ∀ n ∈ S, ∀ i, (p n i).Prime)
    (hmem : ∀ n ∈ S, ∀ i, p n i ∈ T)
    (hreal : ∀ n ∈ S, n = ∏ i, p n i) :
    (∑ n ∈ S, (n.totient : ℝ)⁻¹) ≤
      (∑ q ∈ T, ((q-1 : ℕ) : ℝ)⁻¹)^h := by
  classical
  have hinj : Set.InjOn p (S : Set ℕ) := by
    intro n hn m hm he
    calc
      n = ∏ i, p n i := hreal n hn
      _ = ∏ i, p m i := by rw [he]
      _ = m := (hreal m hm).symm
  have hsub : S.image p ⊆ Fintype.piFinset (fun _ : Fin h => T) := by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
    exact Fintype.mem_piFinset.mpr (hmem n hn)
  calc
    _ ≤ ∑ n ∈ S, reciprocalShiftWeight (p n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnat := totient_prime_product_lower Finset.univ (p n) 1
        (fun i _ => hprime n hn i)
      simp only [Nat.totient_one, one_mul] at hnat
      have hpos : (0 : ℝ) < (∏ i, (p n i-1) : ℕ) := by
        exact_mod_cast Finset.prod_pos
          (fun i _ => Nat.sub_pos_of_lt (hprime n hn i).one_lt)
      have hrec := inv_anti₀ hpos (Nat.cast_le.mpr hnat)
      change (n.totient : ℝ)⁻¹ ≤ ((∏ i, (p n i-1) : ℕ) : ℝ)⁻¹
      rw [congrArg Nat.totient (hreal n hn)]
      exact hrec
    _ = ∑ v ∈ S.image p, reciprocalShiftWeight v :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ v ∈ Fintype.piFinset (fun _ : Fin h => T), reciprocalShiftWeight v :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun v _ _ => reciprocalShiftWeight_nonneg v)
    _ = _ := by rw [ppt_prime_pi_mass]; simp

/-- Summing over all possible factor counts costs only `H+1` times the
largest of the fixed-length bounds. -/
theorem ppt_bounded_length_tail_mass (H : ℕ) (T : Finset ℕ)
    (S : ℕ → Finset ℕ) (p : (h : ℕ) → ℕ → Fin h → ℕ)
    (hprime : ∀ h ≤ H, ∀ n ∈ S h, ∀ i, (p h n i).Prime)
    (hmem : ∀ h ≤ H, ∀ n ∈ S h, ∀ i, p h n i ∈ T)
    (hreal : ∀ h ≤ H, ∀ n ∈ S h, n = ∏ i, p h n i) :
    (∑ h ∈ Finset.range (H+1), ∑ n ∈ S h, (n.totient : ℝ)⁻¹) ≤
      (H+1 : ℕ)*
        (max 1 (∑ q ∈ T, ((q-1 : ℕ) : ℝ)⁻¹))^H := by
  let A : ℝ := ∑ q ∈ T, ((q-1 : ℕ) : ℝ)⁻¹
  have hA : 0 ≤ A := Finset.sum_nonneg (fun q _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ _h ∈ Finset.range (H+1), (max 1 A)^H := by
      apply Finset.sum_le_sum
      intro h hh
      have hhH : h ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
      have hb := ppt_fixed_length_tail_mass (S h) T (p h)
        (hprime h hhH) (hmem h hhH) (hreal h hhH)
      exact hb.trans ((pow_le_pow_left₀ hA (le_max_right _ _) h).trans
        (pow_le_pow_right₀ (le_max_left _ _) hhH))
    _ = _ := by simp [A]

end TotientAsymptotic

end

end OAI
