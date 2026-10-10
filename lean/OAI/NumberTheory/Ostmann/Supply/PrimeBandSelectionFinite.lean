import OAI.NumberTheory.Ostmann.Construction.LogLogPrimeBandSupport
import OAI.NumberTheory.Ostmann.Supply.PrimeBandSelectionBudget

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter Ostmann.Construction
open scoped BigOperators

def sparseBalancedPrimes (d : Decomposition) (δ L : ℝ) (E : Finset ℕ) : Finset ℕ := by
  classical
  exact (logLogPrimeBand ((1/20:ℝ)*L) ((9/10:ℝ)*L)).filter
    (fun p => balancedDensity d p ∧ residueGamma d p≤δ) \ E

theorem sparseBalancedPrimes_properties (d : Decomposition) (δ L : ℝ) (E : Finset ℕ)
    {p : ℕ} (hp : p∈sparseBalancedPrimes d δ L E) :
    p.Prime ∧ (1/20:ℝ)*L<Real.log (Real.log p) ∧
      Real.log (Real.log p)≤(9/10:ℝ)*L ∧ balancedDensity d p ∧
      residueGamma d p≤δ ∧ p∉E := by
  classical
  obtain ⟨hp,hE⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hband,hbal,hγ⟩ := Finset.mem_filter.mp hp
  obtain ⟨hprime,hlo,hhi⟩ := (logLogPrimeBand_mem_iff _ _ _).mp hband
  exact ⟨hprime,hlo,hhi,hbal,hγ,hE⟩

lemma harmonicPrimeMass_mono {P R : Finset ℕ} (hPR : P⊆R) :
    harmonicPrimeMass P≤harmonicPrimeMass R := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hPR
  intro p hp _
  exact div_nonneg zero_le_one (Nat.cast_nonneg _)

lemma harmonicPrimeMass_union_le (P R : Finset ℕ) :
    harmonicPrimeMass (P∪R)≤harmonicPrimeMass P+harmonicPrimeMass R := by
  unfold harmonicPrimeMass
  have he := Finset.sum_union_inter (s₁ := P) (s₂ := R) (f := fun p : ℕ => (1:ℝ)/p)
  have hn : 0≤∑p∈P∩R,(1:ℝ)/p :=
    Finset.sum_nonneg (fun p _ => div_nonneg zero_le_one (Nat.cast_nonneg p))
  linarith

theorem sparseBalancedPrimes_mass_cover (d : Decomposition) (δ L : ℝ) (E : Finset ℕ) :
    harmonicPrimeMass (logLogPrimeBand ((1/20:ℝ)*L) ((9/10:ℝ)*L) \ E)≤
      harmonicPrimeMass (sparseBalancedPrimes d δ L E)+
      harmonicPrimeMass (unbalancedPrimePrefix d (supplyBandCutoff L))+
      harmonicPrimeMass (nonsparsePrimes d δ L) := by
  classical
  have hsub : logLogPrimeBand ((1/20:ℝ)*L) ((9/10:ℝ)*L) \ E ⊆
      (sparseBalancedPrimes d δ L E ∪ unbalancedPrimePrefix d (supplyBandCutoff L)) ∪
        nonsparsePrimes d δ L := by
    intro p hp
    obtain ⟨hband,hE⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hprime,hlo,hhi⟩ := (logLogPrimeBand_mem_iff _ _ _).mp hband
    have hupper : p≤ supplyBandCutoff L := by
      exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hband).1).1).2
    by_cases hbal : balancedDensity d p
    · by_cases hγ : residueGamma d p≤δ
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hband,hbal,hγ⟩,hE⟩
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr (by unfold supplyBandCutoff at hupper; omega),hprime,hlo.le,hhi,hbal.1,hbal.2,
          (lt_of_not_ge hγ).le⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hupper,hprime⟩,hbal⟩
  calc
    _ ≤ harmonicPrimeMass ((sparseBalancedPrimes d δ L E ∪
      unbalancedPrimePrefix d (supplyBandCutoff L)) ∪ nonsparsePrimes d δ L) :=
        harmonicPrimeMass_mono hsub
    _ ≤ harmonicPrimeMass (sparseBalancedPrimes d δ L E ∪
      unbalancedPrimePrefix d (supplyBandCutoff L))+harmonicPrimeMass (nonsparsePrimes d δ L) :=
        harmonicPrimeMass_union_le _ _
    _ ≤ _ := by
      have h := harmonicPrimeMass_union_le (sparseBalancedPrimes d δ L E)
        (unbalancedPrimePrefix d (supplyBandCutoff L))
      linarith

end Ostmann.Supply

end

end OAI
