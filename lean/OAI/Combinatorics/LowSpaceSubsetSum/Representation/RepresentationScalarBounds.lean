import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPreparedFields
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordWidthBounds

namespace OAI

/-! # Word-sized stored prime moduli and their product -/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationScalarBounds

variable {n : ℕ}

theorem prefix_bound (R : RepresentationSetup n) (hn : 1 ≤ n)
    (z : RepresentationSetup.Layout n) (p : R.PrimeSpace z) (j : Fin 3) :
    prefixModulus p.val j ≤ 2 ^ (3 * n) := by
  obtain ⟨hab, hc⟩ := Finset.mem_product.mp p.property
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  have factor {ell a : ℕ} (he : ell ≤ n) (h : a ∈ factorRange ell) : a ≤ 2 ^ n := by
    have hu : a ≤ 2 ^ ell := by exact_mod_cast (factor_size_bounds hn he h).2
    exact hu.trans (Nat.pow_le_pow_right (by decide) he)
  have ha' := factor (R.factorExponents_le_n z 0) ha
  have hb' := factor (R.factorExponents_le_n z 1) hb
  have hc' := factor (R.factorExponents_le_n z 2) hc
  have hab' : p.val.1.1 * p.val.1.2 ≤ 2 ^ (2 * n) := by
    calc
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul ha' hb'
      _ = _ := by rw [← pow_add]; congr 1; omega
  have habc : p.val.1.1 * p.val.1.2 * p.val.2 ≤ 2 ^ (3 * n) := by
    calc
      _ ≤ 2 ^ (2 * n) * 2 ^ n := Nat.mul_le_mul hab' hc'
      _ = _ := by rw [← pow_add]; congr 1; omega
  fin_cases j
  · exact habc
  · exact hab'.trans (Nat.pow_le_pow_right (by decide) (by omega))
  · exact ha'.trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem moduli_bound (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d) (j : Fin 3) :
    d.residues.primes.moduli[j.val] ≤ 2 ^ (3 * n) := by
  obtain ⟨_, _, hr, _⟩ := RepresentationExtraPreparation.source I hn hlog s d h
  obtain ⟨_, _, hp, _⟩ := RepresentationResiduePreparation.source I hn hlog s.1 d.residues hr
  rw [RepresentationPrimePreparation.moduli_ideal I hn hlog s.1.1 d.residues.primes hp j]
  exact prefix_bound _ (by omega) _ _ j

theorem extra_bound (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d) : d.q ≤ 2 ^ n := by
  obtain ⟨history, _, _, hq⟩ := RepresentationExtraPreparation.source I hn hlog s d h
  rw [hq]
  have hr := (canonicalRepresentationData I).zeroSetup.extraPrimeParameter_range
    history.1.1.1.1.1 (by omega : 100 ≤ n)
  exact (primeRange_lt hr.1 history.2.property).le.trans (Nat.pow_le_pow_right (by decide) hr.2)

theorem product_fits (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d) :
    d.residues.primes.moduli[0] * d.q < 2 ^ wordWidth I := by
  calc
    _ ≤ 2 ^ (3 * n) * 2 ^ n := Nat.mul_le_mul (moduli_bound I hn hlog s d h 0)
      (extra_bound I hn hlog s d h)
    _ = 2 ^ (4 * n) := by rw [← pow_add]; congr 1; omega
    _ < _ := Nat.pow_lt_pow_right (by decide) (by unfold wordWidth inputScale; omega)

end LowSpaceSubsetSum.RepresentationScalarBounds

end

end OAI
