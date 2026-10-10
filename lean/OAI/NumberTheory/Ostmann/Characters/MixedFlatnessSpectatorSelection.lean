import OAI.NumberTheory.Ostmann.Characters.MixedFlatnessSpectatorHarmonic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Characters
open Construction QuadraticCenter Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def mixedSpectatorPrimes (d : Decomposition) (δ L : ℝ) : Finset ℕ :=
  (balancedPrimePart d (logLogPrimeBand ((1/2000:ℝ)*L) ((1/1000:ℝ)*L))).filter
    (fun p=>mixedPrimeBias d p<δ)

theorem mem_mixedSpectatorPrimes (d : Decomposition) (δ L : ℝ) (p : ℕ) :
    p∈mixedSpectatorPrimes d δ L ↔ p.Prime ∧
      (1/2000:ℝ)*L<Real.log (Real.log p) ∧ Real.log (Real.log p)≤(1/1000:ℝ)*L ∧
      Supply.balancedDensity d p ∧ mixedPrimeBias d p<δ := by
  simp only [mixedSpectatorPrimes,balancedPrimePart,Finset.mem_filter,logLogPrimeBand_mem_iff]
  tauto

theorem unbalanced_spectator_band_subset (d : Decomposition) {L : ℝ} (_hL : 0≤L) :
    (logLogPrimeBand ((1/2000:ℝ)*L) ((1/1000:ℝ)*L)).filter
      (fun p=>¬Supply.balancedDensity d p) ⊆
    Supply.unbalancedPrimePrefix d (Supply.supplyBandCutoff L) := by
  intro p hp
  obtain ⟨hband,hbad⟩ := Finset.mem_filter.mp hp
  obtain ⟨hprime,hlo,hhi⟩ := (logLogPrimeBand_mem_iff _ _ _).mp hband
  apply Finset.mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_,hprime⟩,hbad⟩
  apply Nat.le_floor
  exact (prime_loglog_le_iff hprime _).mp (hhi.trans (by nlinarith))

theorem eventually_mixedSpectator_mass (d : Decomposition)
    (hhigher : HigherHarmonicBandInput d (1/2000) (1/1000))
    (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ L : ℝ in atTop, L/5000≤harmonicPrimeMass (mixedSpectatorPrimes d δ L) := by
  have hmixed := eventually_mixedBad_harmonic_band_le d
    (by norm_num : (0:ℝ)<1/2000) (by norm_num : (1/2000:ℝ)<1/1000)
    hhigher δ (1/40000) hδ (by norm_num)
  filter_upwards [hmixed,Supply.unbalancedPrimePrefix_mass_small d (by norm_num : (0:ℝ)<1/40000),
    logLogPrimeBand_mass_eventually (by norm_num : (0:ℝ)≤1/2000)
      (by norm_num : (1/2000:ℝ)<1/1000),eventually_ge_atTop (0:ℝ)]
    with L hmix hunbal hmass hL
  let P := logLogPrimeBand ((1/2000:ℝ)*L) ((1/1000:ℝ)*L)
  have hb := (hmass ∅ (by simp)).2.1
  simp only [Finset.sdiff_empty] at hb
  have hu : harmonicPrimeMass (P.filter (fun p=>¬Supply.balancedDensity d p))≤L/40000 := by
    have hh := (Supply.harmonicPrimeMass_mono (unbalanced_spectator_band_subset d hL)).trans hunbal
    change harmonicPrimeMass (P.filter (fun p=>¬Supply.balancedDensity d p))≤(1/40000:ℝ)*L at hh
    linarith
  have hsplit : harmonicPrimeMass (balancedPrimePart d P)+
      harmonicPrimeMass (P.filter (fun p=>¬Supply.balancedDensity d p))=harmonicPrimeMass P :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hsplit' : harmonicPrimeMass (mixedSpectatorPrimes d δ L)+
      harmonicPrimeMass (mixedBadPrimes d (balancedPrimePart d P) δ)=
      harmonicPrimeMass (balancedPrimePart d P) := by
    have hh := Finset.sum_filter_add_sum_filter_not (balancedPrimePart d P)
      (fun p=>mixedPrimeBias d p<δ) (fun p=>(1:ℝ)/p)
    simpa only [not_lt,mixedSpectatorPrimes,mixedBadPrimes,harmonicPrimeMass,P] using hh
  change harmonicPrimeMass (mixedBadPrimes d (balancedPrimePart d P) δ)≤(1/40000:ℝ)*L at hmix
  change ((1/1000:ℝ)-1/2000)*L/2≤harmonicPrimeMass P at hb
  linarith

theorem mixedSpectator_prime_support (d : Decomposition) (δ L : ℝ) {p : ℕ}
    (hp : p∈mixedSpectatorPrimes d δ L) :
    p.Prime ∧ Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℝ) ∧
      Real.log (p:ℝ)≤Real.exp ((1/1000:ℝ)*L) ∧
      Supply.balancedDensity d p ∧ mixedPrimeBias d p<δ := by
  obtain ⟨hprime,hlo,hhi,hbal,hflat⟩ := (mem_mixedSpectatorPrimes d δ L p).mp hp
  have hl : 0<Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
  have hlow := Real.exp_le_exp.mpr hlo.le
  have hupp := Real.exp_le_exp.mpr hhi
  rw [Real.exp_log hl] at hlow hupp
  exact ⟨hprime,hlow,hupp,hbal,hflat⟩

end Ostmann.Characters

end

end OAI
