import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueNormSumBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealizationCanonical

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkResidueNormSum
open Construction HistoryBulkSpectatorProduct HistoryCRTIntegration HistoryFrequencyResidues

theorem actual_bulk_modulus_ne_zero {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (K : ℕ) :
    outside.prod*(pairedFrequencyProduct h k)^(K+2) ≠ 0 :=
  mul_ne_zero (HistorySignedSpectatorDiagramAverage.outsideNeZero hp).out (pow_ne_zero _ (pairedFrequencyProduct_ne_zero hs ks))

theorem sum_norm_canonicalUnitTest_actual_modulus (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m)) (K : ℕ)
    (zD : UnitPair outside.prod) (zR : UnitPair ((pairedFrequencyProduct h k)^(K+2))) :
    let N := outside.prod*(pairedFrequencyProduct h k)^(K+2)
    letI : NeZero N := ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
    (∑x, ‖canonicalUnitTest d h k hs ks hp hV σ K N
      (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _) zD zR x‖) ≤
        (N:ℝ)^(2^l*m+2^(l+1)) := by
  let : NeZero (outside.prod*(pairedFrequencyProduct h k)^(K+2)) :=
    ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
  exact sum_norm_canonicalUnitTest_le d h k hs ks hp hV σ K _ _ _ zD zR

theorem sum_norm_canonicalMixedTest_actual_modulus (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m)) (K : ℕ)
    (zD : MixedPair outside.prod) (zR : MixedPair ((pairedFrequencyProduct h k)^(K+2))) :
    let N := outside.prod*(pairedFrequencyProduct h k)^(K+2)
    letI : NeZero N := ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
    (∑x, ‖canonicalMixedTest d h k hs ks hp hV σ K N
      (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _) zD zR x‖) ≤
        (N:ℝ)^(2^l*m+2^(l+1)) := by
  let : NeZero (outside.prod*(pairedFrequencyProduct h k)^(K+2)) :=
    ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
  exact sum_norm_canonicalMixedTest_le d h k hs ks hp hV σ K _ _ _ zD zR

theorem sum_norm_independentUnitTest_actual_modulus (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m)) (K : ℕ)
    (zD : UnitPair outside.prod) (zR : UnitPair ((pairedFrequencyProduct h k)^(K+2))) :
    let N := outside.prod*(pairedFrequencyProduct h k)^(K+2)
    letI : NeZero N := ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
    (∑x, ‖independentUnitTest d h k hs ks hp hV σ K N
      (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _) zD zR x‖) ≤
        (N:ℝ)^(2^l*m+2^(l+1)) := by
  let : NeZero (outside.prod*(pairedFrequencyProduct h k)^(K+2)) :=
    ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
  exact sum_norm_independentUnitTest_le d h k hs ks hp hV σ K _ _ _ zD zR

theorem sum_norm_independentMixedTest_actual_modulus (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m)) (K : ℕ)
    (zD : MixedPair outside.prod) (zR : MixedPair ((pairedFrequencyProduct h k)^(K+2))) :
    let N := outside.prod*(pairedFrequencyProduct h k)^(K+2)
    letI : NeZero N := ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
    (∑x, ‖independentMixedTest d h k hs ks hp hV σ K N
      (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _) zD zR x‖) ≤
        (N:ℝ)^(2^l*m+2^(l+1)) := by
  let : NeZero (outside.prod*(pairedFrequencyProduct h k)^(K+2)) :=
    ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
  exact sum_norm_independentMixedTest_le d h k hs ks hp hV σ K _ _ _ zD zR

end Ostmann.Arithmetic.HistoryBulkResidueNormSum

end

end OAI
