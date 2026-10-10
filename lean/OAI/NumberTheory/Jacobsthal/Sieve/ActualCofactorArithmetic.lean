import OAI.NumberTheory.Jacobsthal.Partitions.SourceDenseCellContradiction

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseBoxApplication
open ErdosCofactorChoices ErdosInverseCells ErdosInverseRefinement ErdosInverseBoxHeight
open NumberTheoryLean.LogarithmicBinScale NumberTheoryLean.LogarithmicBinEndpoints
  NumberTheoryLean.LogarithmicBinPartition

theorem actual_excluded_bin_coprime {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ)
    (i : Fin (binCount (sourceW z) z xi)) (hi : m i = 0)
    (q : ℕ) (hq : q ∈ cofactorChoices (actualBins z xi) m) :
    ∀ p ∈ actualBins z xi i,q.Coprime p :=
  cofactor_coprime_excluded_bin (actualBins z xi) m
    (fun j _ hp => (bin_prime_in_source hw hwz hxi j hp).1)
    (fun i j hij => bins_pairwise_disjoint hw hwz hxi i j hij) i hi q hq

theorem actual_distinct_bins_coprime {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (i j : Fin (binCount (sourceW z) z xi)) (hij : i ≠ j) :
    ∀ p ∈ actualBins z xi i,∀ u ∈ actualBins z xi j,p.Coprime u :=
  distinct_bins_coprime (actualBins z xi)
    (fun j _ hp => (bin_prime_in_source hw hwz hxi j hp).1)
    (fun i j hij => bins_pairwise_disjoint hw hwz hxi i j hij) i j hij

theorem actual_parent_small_coprime {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (m : Fin (binCount (sourceW z) z xi) → ℕ)
    (q : ℕ) (hq : q ∈ cofactorChoices (actualBins z xi) m)
    (i : Fin (binCount (sourceW z) z xi)) (p : ℕ) (hp : p ∈ actualBins z xi i) :
    ∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q).Coprime t := by
  intro t ht htw
  have hqcop := cofactor_coprime_small (actualBins z xi) m
    (fun j _ hp => (bin_prime_in_source hw hwz hxi j hp).1) (sourceW z)
    (fun j _ hp => (bin_prime_in_source hw hwz hxi j hp).2.1) q hq t ht htw
  apply Nat.Coprime.mul_left _ hqcop
  have hps := bin_prime_in_source hw hwz hxi i hp
  apply (Nat.coprime_primes hps.1 ht).mpr
  intro he
  subst p
  linarith [hps.2.1]

theorem actual_source_cofactor_inflation {z xi : ℝ} (hw : 0 < sourceW z) (hwz : sourceW z < z)
    (hxi : 0 < xi) (Clen : ℝ) (m : Fin (binCount (sourceW z) z xi) → ℕ)
    (hm : ((∑ i,m i : ℕ) : ℝ) ≤ Clen*Real.log (sourceB z))
    (q : ℕ) (hq : q ∈ cofactorChoices (actualBins z xi) m) :
    1 ≤ cofactorScale z xi m/(q : ℝ) ∧
      cofactorScale z xi m/(q : ℝ) ≤
        (1+effectiveWidth (sourceW z) z xi)^(Clen*Real.log (sourceB z)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast actual_cofactor_positive hw hwz hxi m q hq
  have htheta := effectiveWidth_pos hw hwz hxi
  have hF : 0 < 1+effectiveWidth (sourceW z) z xi := by linarith
  have hrange := actual_cofactor_effective_range hw hwz hxi m q hq
  refine ⟨(one_le_div hqpos).mpr hrange.2,?_⟩
  calc
    _ ≤ (1+effectiveWidth (sourceW z) z xi)^(∑ i,m i) := by
      apply (div_le_iff₀ hqpos).mpr
      have hh := (div_le_iff₀ (pow_pos hF _)).mp hrange.1
      nlinarith
    _ = (1+effectiveWidth (sourceW z) z xi)^((∑ i,m i : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hm

end ErdosInverseBoxApplication

end

end Erdos970

end OAI
