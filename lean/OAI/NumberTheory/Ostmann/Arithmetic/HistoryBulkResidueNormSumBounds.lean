import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueNormSumCard
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueNormSumTests

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkResidueNormSum
open Construction HistoryBulkSpectatorProduct HistoryCRTIntegration HistoryFrequencyResidues

theorem sum_norm_canonicalUnitTest_le (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (K N : ℕ) [NeZero N] (hD : outside.prod∣N) (hR : (pairedFrequencyProduct h k)^(K+2)∣N)
    (zD : UnitPair outside.prod) (zR : UnitPair ((pairedFrequencyProduct h k)^(K+2)))
    : (∑x, ‖canonicalUnitTest d h k hs ks hp hV σ K N hD hR zD zR x‖) ≤
      (N:ℝ)^(2^l*m+2^(l+1)) := by
  exact ordered_sum_norm_le_modulus_power (Nat.le_of_dvd (NeZero.pos N) hD)
    (canonicalUnitTest d h k hs ks hp hV σ K N hD hR zD zR) (canonicalUnitTest_norm_le d h k hs ks hp hV σ K N hD hR zD zR)

theorem sum_norm_canonicalMixedTest_le (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (K N : ℕ) [NeZero N] (hD : outside.prod∣N) (hR : (pairedFrequencyProduct h k)^(K+2)∣N)
    (zD : MixedPair outside.prod) (zR : MixedPair ((pairedFrequencyProduct h k)^(K+2)))
    : (∑x, ‖canonicalMixedTest d h k hs ks hp hV σ K N hD hR zD zR x‖) ≤
      (N:ℝ)^(2^l*m+2^(l+1)) := by
  exact ordered_sum_norm_le_modulus_power (Nat.le_of_dvd (NeZero.pos N) hD)
    (canonicalMixedTest d h k hs ks hp hV σ K N hD hR zD zR) (canonicalMixedTest_norm_le d h k hs ks hp hV σ K N hD hR zD zR)

theorem sum_norm_independentUnitTest_le (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (K N : ℕ) [NeZero N] (hD : outside.prod∣N) (hR : (pairedFrequencyProduct h k)^(K+2)∣N)
    (zD : UnitPair outside.prod) (zR : UnitPair ((pairedFrequencyProduct h k)^(K+2)))
    : (∑x, ‖independentUnitTest d h k hs ks hp hV σ K N hD hR zD zR x‖) ≤
      (N:ℝ)^(2^l*m+2^(l+1)) := by
  exact ordered_sum_norm_le_modulus_power (Nat.le_of_dvd (NeZero.pos N) hD)
    (independentUnitTest d h k hs ks hp hV σ K N hD hR zD zR) (independentUnitTest_norm_le d h k hs ks hp hV σ K N hD hR zD zR)

theorem sum_norm_independentMixedTest_le (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (K N : ℕ) [NeZero N] (hD : outside.prod∣N) (hR : (pairedFrequencyProduct h k)^(K+2)∣N)
    (zD : MixedPair outside.prod) (zR : MixedPair ((pairedFrequencyProduct h k)^(K+2)))
    : (∑x, ‖independentMixedTest d h k hs ks hp hV σ K N hD hR zD zR x‖) ≤
      (N:ℝ)^(2^l*m+2^(l+1)) := by
  exact ordered_sum_norm_le_modulus_power (Nat.le_of_dvd (NeZero.pos N) hD)
    (independentMixedTest d h k hs ks hp hV σ K N hD hR zD zR) (independentMixedTest_norm_le d h k hs ks hp hV σ K N hD hR zD zR)

end Ostmann.Arithmetic.HistoryBulkResidueNormSum

end

end OAI
