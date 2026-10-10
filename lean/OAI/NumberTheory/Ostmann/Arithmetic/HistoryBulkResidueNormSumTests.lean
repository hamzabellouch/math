import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueNormSumDiagram
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueNormSumFrequency

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkResidueNormSum
open Construction HistoryBulkSpectatorProduct HistoryCRTIntegration HistoryFrequencyResidues

def canonicalUnitTest (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (K N : ℕ) (hD : outside.prod∣N) (hR : (pairedFrequencyProduct h k)^(K+2)∣N)
    (zD : UnitPair outside.prod) (zR : UnitPair ((pairedFrequencyProduct h k)^(K+2)))
    (x : Fin (2^l)×Fin m → (ZMod N)ˣ) : ℂ :=
  unitTest h k hs ks hp hV σ (residueTransform d) zD (fun i => ZMod.unitsMap hD (x i)) *
    canonicalRTest K h k ((zR.1:ZMod ((pairedFrequencyProduct h k)^(K+2))),(zR.2:ZMod ((pairedFrequencyProduct h k)^(K+2)))) (fun i => ZMod.unitsMap hR (x i))

theorem canonicalUnitTest_norm_le (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (K N : ℕ) (hD : outside.prod∣N) (hR : (pairedFrequencyProduct h k)^(K+2)∣N)
    (zD : UnitPair outside.prod) (zR : UnitPair ((pairedFrequencyProduct h k)^(K+2)))
    (x : Fin (2^l)×Fin m → (ZMod N)ˣ) :
    ‖canonicalUnitTest d h k hs ks hp hV σ K N hD hR zD zR x‖ ≤ (outside.prod:ℝ)^(2^(l+1)) := by
  rw [canonicalUnitTest, norm_mul]
  exact (mul_le_mul (actual_unitTest_norm_le d h k hs ks hp hV σ _ _)
    (canonicalRTest_norm_le K h k _ _) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

def canonicalMixedTest (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (K N : ℕ) (hD : outside.prod∣N) (hR : (pairedFrequencyProduct h k)^(K+2)∣N)
    (zD : MixedPair outside.prod) (zR : MixedPair ((pairedFrequencyProduct h k)^(K+2)))
    (x : Fin (2^l)×Fin m → (ZMod N)ˣ) : ℂ :=
  mixedTest h k hs ks hp hV σ (residueTransform d) zD (fun i => ZMod.unitsMap hD (x i)) *
    canonicalRTest K h k ((zR.1:ZMod ((pairedFrequencyProduct h k)^(K+2))),(zR.2:ZMod ((pairedFrequencyProduct h k)^(K+2)))) (fun i => ZMod.unitsMap hR (x i))

theorem canonicalMixedTest_norm_le (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (K N : ℕ) (hD : outside.prod∣N) (hR : (pairedFrequencyProduct h k)^(K+2)∣N)
    (zD : MixedPair outside.prod) (zR : MixedPair ((pairedFrequencyProduct h k)^(K+2)))
    (x : Fin (2^l)×Fin m → (ZMod N)ˣ) :
    ‖canonicalMixedTest d h k hs ks hp hV σ K N hD hR zD zR x‖ ≤ (outside.prod:ℝ)^(2^(l+1)) := by
  rw [canonicalMixedTest, norm_mul]
  exact (mul_le_mul (actual_mixedTest_norm_le d h k hs ks hp hV σ _ _)
    (canonicalRTest_norm_le K h k _ _) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

def independentUnitTest (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (K N : ℕ) (hD : outside.prod∣N) (hR : (pairedFrequencyProduct h k)^(K+2)∣N)
    (zD : UnitPair outside.prod) (zR : UnitPair ((pairedFrequencyProduct h k)^(K+2)))
    (x : Fin (2^l)×Fin m → (ZMod N)ˣ) : ℂ :=
  unitTest h k hs ks hp hV σ (residueTransform d) zD (fun i => ZMod.unitsMap hD (x i)) *
    independentRTest K h k σ ((zR.1:ZMod ((pairedFrequencyProduct h k)^(K+2))),(zR.2:ZMod ((pairedFrequencyProduct h k)^(K+2)))) (fun i => ZMod.unitsMap hR (x i))

theorem independentUnitTest_norm_le (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (K N : ℕ) (hD : outside.prod∣N) (hR : (pairedFrequencyProduct h k)^(K+2)∣N)
    (zD : UnitPair outside.prod) (zR : UnitPair ((pairedFrequencyProduct h k)^(K+2)))
    (x : Fin (2^l)×Fin m → (ZMod N)ˣ) :
    ‖independentUnitTest d h k hs ks hp hV σ K N hD hR zD zR x‖ ≤ (outside.prod:ℝ)^(2^(l+1)) := by
  rw [independentUnitTest, norm_mul]
  exact (mul_le_mul (actual_unitTest_norm_le d h k hs ks hp hV σ _ _)
    (independentRTest_norm_le K h k σ _ _) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

def independentMixedTest (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (K N : ℕ) (hD : outside.prod∣N) (hR : (pairedFrequencyProduct h k)^(K+2)∣N)
    (zD : MixedPair outside.prod) (zR : MixedPair ((pairedFrequencyProduct h k)^(K+2)))
    (x : Fin (2^l)×Fin m → (ZMod N)ˣ) : ℂ :=
  mixedTest h k hs ks hp hV σ (residueTransform d) zD (fun i => ZMod.unitsMap hD (x i)) *
    independentRTest K h k σ ((zR.1:ZMod ((pairedFrequencyProduct h k)^(K+2))),(zR.2:ZMod ((pairedFrequencyProduct h k)^(K+2)))) (fun i => ZMod.unitsMap hR (x i))

theorem independentMixedTest_norm_le (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ}
    {outside : List ℕ} (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (K N : ℕ) (hD : outside.prod∣N) (hR : (pairedFrequencyProduct h k)^(K+2)∣N)
    (zD : MixedPair outside.prod) (zR : MixedPair ((pairedFrequencyProduct h k)^(K+2)))
    (x : Fin (2^l)×Fin m → (ZMod N)ˣ) :
    ‖independentMixedTest d h k hs ks hp hV σ K N hD hR zD zR x‖ ≤ (outside.prod:ℝ)^(2^(l+1)) := by
  rw [independentMixedTest, norm_mul]
  exact (mul_le_mul (actual_mixedTest_norm_le d h k hs ks hp hV σ _ _)
    (independentRTest_norm_le K h k σ _ _) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

end Ostmann.Arithmetic.HistoryBulkResidueNormSum

end

end OAI
