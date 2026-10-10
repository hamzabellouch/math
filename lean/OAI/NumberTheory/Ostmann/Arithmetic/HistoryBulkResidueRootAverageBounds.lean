import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueRootAverageBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkResidueRootAverage
open Construction ResidueHaar HistoryBulkResidueNormSum
open HistoryBulkSpectatorProduct HistoryFrequencyResidues HistoryCRTIntegration
open HistoryBulkDiagramFrequencyAverage

variable (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
  (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
  (σ : Equiv.Perm (Fin (2^l)×Fin m)) (K : ℕ)

theorem sum_norm_canonicalUnit_le :
    letI : NeZero (outside.prod*(pairedFrequencyProduct h k)^(K+2)) :=
      ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
    (∑x,‖canonicalUnit d h k hs ks hp hV σ K x‖)≤
      ((outside.prod*(pairedFrequencyProduct h k)^(K+2):ℕ):ℝ)^(2^l*m+2^(l+1)) := by
  let : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
  let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  let : NeZero (outside.prod*(pairedFrequencyProduct h k)^(K+2)) :=
    ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
  exact sum_norm_nested_average_le
    (fun (zD : UnitPair outside.prod) (zR : UnitPair ((pairedFrequencyProduct h k)^(K+2))) x=>
      canonicalUnitTest d h k hs ks hp hV σ K _ (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _) zD zR x)
    _ (fun zD zR=>sum_norm_canonicalUnitTest_le d h k hs ks hp hV σ K _ _ _ zD zR)

theorem sum_norm_canonicalMixed_le :
    letI : NeZero (outside.prod*(pairedFrequencyProduct h k)^(K+2)) :=
      ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
    (∑x,‖canonicalMixed d h k hs ks hp hV σ K x‖)≤
      ((outside.prod*(pairedFrequencyProduct h k)^(K+2):ℕ):ℝ)^(2^l*m+2^(l+1)) := by
  let : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
  let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  let : NeZero (outside.prod*(pairedFrequencyProduct h k)^(K+2)) :=
    ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
  exact sum_norm_nested_average_le
    (fun (zD : MixedPair outside.prod) (zR : MixedPair ((pairedFrequencyProduct h k)^(K+2))) x=>
      canonicalMixedTest d h k hs ks hp hV σ K _ (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _) zD zR x)
    _ (fun zD zR=>sum_norm_canonicalMixedTest_le d h k hs ks hp hV σ K _ _ _ zD zR)

theorem sum_norm_independentUnit_le :
    letI : NeZero (outside.prod*(pairedFrequencyProduct h k)^(K+2)) :=
      ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
    (∑x,‖independentUnit d h k hs ks hp hV σ K x‖)≤
      ((outside.prod*(pairedFrequencyProduct h k)^(K+2):ℕ):ℝ)^(2^l*m+2^(l+1)) := by
  let : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
  let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  let : NeZero (outside.prod*(pairedFrequencyProduct h k)^(K+2)) :=
    ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
  exact sum_norm_nested_average_le
    (fun (zD : UnitPair outside.prod) (zR : UnitPair ((pairedFrequencyProduct h k)^(K+2))) x=>
      independentUnitTest d h k hs ks hp hV σ K _ (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _) zD zR x)
    _ (fun zD zR=>sum_norm_independentUnitTest_le d h k hs ks hp hV σ K _ _ _ zD zR)

theorem sum_norm_independentMixed_le :
    letI : NeZero (outside.prod*(pairedFrequencyProduct h k)^(K+2)) :=
      ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
    (∑x,‖independentMixed d h k hs ks hp hV σ K x‖)≤
      ((outside.prod*(pairedFrequencyProduct h k)^(K+2):ℕ):ℝ)^(2^l*m+2^(l+1)) := by
  let : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
  let : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  let : NeZero (outside.prod*(pairedFrequencyProduct h k)^(K+2)) :=
    ⟨actual_bulk_modulus_ne_zero h k hs ks hp K⟩
  exact sum_norm_nested_average_le
    (fun (zD : MixedPair outside.prod) (zR : MixedPair ((pairedFrequencyProduct h k)^(K+2))) x=>
      independentMixedTest d h k hs ks hp hV σ K _ (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _) zD zR x)
    _ (fun zD zR=>sum_norm_independentMixedTest_le d h k hs ks hp hV σ K _ _ _ zD zR)

end Ostmann.Arithmetic.HistoryBulkResidueRootAverage

end

end OAI
