import OAI.NumberTheory.Ostmann.Supply.PrimeBandSelectionFinite

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter Ostmann.Construction
open scoped BigOperators

theorem sparseBalancedPrimes_mass_eventually (d : Decomposition) :
    ∀ᶠ L : ℝ in atTop, ∀ δ : ℝ, ∀ E : Finset ℕ, E.card≤2 →
      harmonicPrimeMass (nonsparsePrimes d δ L)<(3/20:ℝ)*L →
      (17/25:ℝ)*L≤harmonicPrimeMass (sparseBalancedPrimes d δ L E) ∧
      harmonicPrimeMass (sparseBalancedPrimes d δ L E)≤(43/50:ℝ)*L := by
  classical
  obtain ⟨C,hC,hband⟩ := logLogPrimeBand_mass_error
  have hunbalanced := unbalancedPrimePrefix_mass_small d (by norm_num : (0:ℝ)<1/100)
  filter_upwards [hunbalanced,eventually_ge_atTop (max 0 (100*C))] with L hu hL
  have hL0 : 0≤L := (le_max_left _ _).trans hL
  have hLC : 100*C≤L := (le_max_right _ _).trans hL
  intro δ E hE hnon
  have hmass := hband ((1/20:ℝ)*L) ((9/10:ℝ)*L) (by positivity)
    (by nlinarith) E hE
  obtain ⟨hlo,hhi⟩ := abs_le.mp hmass
  have hcover := sparseBalancedPrimes_mass_cover d δ L E
  constructor
  · linarith
  · have hs : sparseBalancedPrimes d δ L E ⊆
        logLogPrimeBand ((1/20:ℝ)*L) ((9/10:ℝ)*L) \ E := by
      intro p hp
      obtain ⟨hp,hE⟩ := Finset.mem_sdiff.mp hp
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hp).1,hE⟩
    have hm := harmonicPrimeMass_mono hs
    linarith

theorem exists_sparse_balanced_prime_set (d : Decomposition) :
    ∀ᶠ L : ℝ in atTop, ∀ δ : ℝ, ∀ E : Finset ℕ, E.card≤2 →
      (∑p∈nonsparsePrimes d δ L,(1:ℝ)/p)<(3/20:ℝ)*L →
      ∃ P : Finset ℕ,
        (∀p∈P,p.Prime ∧ (1/20:ℝ)*L<Real.log (Real.log p) ∧
          Real.log (Real.log p)≤(9/10:ℝ)*L ∧
          (1/3:ℝ)≤residueDensityTotal d p ∧ residueDensityTotal d p≤(2/3:ℝ) ∧
          residueGamma d p≤δ ∧ p∉E) ∧
        (17/25:ℝ)*L≤(∑p∈P,(1:ℝ)/p) ∧ (∑p∈P,(1:ℝ)/p)≤(43/50:ℝ)*L := by
  filter_upwards [sparseBalancedPrimes_mass_eventually d] with L hL
  intro δ E hE hnon
  obtain ⟨hlo,hhi⟩ := hL δ E hE hnon
  refine ⟨sparseBalancedPrimes d δ L E,?_,hlo,hhi⟩
  intro p hp
  obtain ⟨hprime,hlo,hhi,hbal,hγ,hE⟩ := sparseBalancedPrimes_properties d δ L E hp
  exact ⟨hprime,hlo,hhi,hbal.1,hbal.2,hγ,hE⟩

end Ostmann.Supply

end

end OAI
