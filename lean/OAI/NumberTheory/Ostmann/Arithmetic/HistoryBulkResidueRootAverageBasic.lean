import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkDiagramFrequencyAverageCRT
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueNormSumActual

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkResidueRootAverage
open Construction Characters ResidueHaar HistoryBulkResidueNormSum
open HistoryBulkSpectatorProduct HistoryFrequencyResidues HistoryCRTIntegration

theorem sum_norm_average_le {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (f : α → ι → ℂ) (C : ℝ) (hf : ∀a, (∑i,‖f a i‖)≤C) :
    (∑i,‖average (fun a=>f a i)‖)≤C := by
  calc
    _ ≤ ∑i,BinaryExposure.avg (fun a=>‖f a i‖) := by
      apply Finset.sum_le_sum
      intro i _
      exact HistoryBulkDiagramFrequencyAverage.norm_average_le_avg_norm _
    _ = BinaryExposure.avg (fun a=>∑i,‖f a i‖) := by
      simp only [BinaryExposure.avg,←Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ BinaryExposure.avg (fun _ : α=>C) := BinaryExposure.avg_mono _ _ hf
    _ = C := BinaryExposure.avg_const C

theorem sum_norm_nested_average_le {α β ι : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] [Fintype ι]
    (f : α → β → ι → ℂ) (C : ℝ) (hf : ∀a b,(∑i,‖f a b i‖)≤C) :
    (∑i,‖average (fun a=>average (fun b=>f a b i))‖)≤C :=
  sum_norm_average_le _ C (fun a=>sum_norm_average_le (f a) C (hf a))

variable (d : Decomposition) {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
  (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
  (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
  (σ : Equiv.Perm (Fin (2^l)×Fin m)) (K : ℕ)

def canonicalUnit
    (x : Fin (2^l)×Fin m → (ZMod (outside.prod*(pairedFrequencyProduct h k)^(K+2)))ˣ) : ℂ := by
  letI : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
  letI : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  exact average (fun zD : UnitPair outside.prod=>
    average (fun zR : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>
      canonicalUnitTest d h k hs ks hp hV σ K _
        (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _) zD zR x))

def canonicalMixed
    (x : Fin (2^l)×Fin m → (ZMod (outside.prod*(pairedFrequencyProduct h k)^(K+2)))ˣ) : ℂ := by
  letI : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
  letI : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  exact average (fun zD : MixedPair outside.prod=>
    average (fun zR : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>
      canonicalMixedTest d h k hs ks hp hV σ K _
        (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _) zD zR x))

def independentUnit
    (x : Fin (2^l)×Fin m → (ZMod (outside.prod*(pairedFrequencyProduct h k)^(K+2)))ˣ) : ℂ := by
  letI : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
  letI : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  exact average (fun zD : UnitPair outside.prod=>
    average (fun zR : UnitPair ((pairedFrequencyProduct h k)^(K+2))=>
      independentUnitTest d h k hs ks hp hV σ K _
        (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _) zD zR x))

def independentMixed
    (x : Fin (2^l)×Fin m → (ZMod (outside.prod*(pairedFrequencyProduct h k)^(K+2)))ˣ) : ℂ := by
  letI : NeZero outside.prod := HistorySignedSpectatorDiagramAverage.outsideNeZero hp
  letI : NeZero (pairedFrequencyProduct h k) := ⟨pairedFrequencyProduct_ne_zero hs ks⟩
  exact average (fun zD : MixedPair outside.prod=>
    average (fun zR : MixedPair ((pairedFrequencyProduct h k)^(K+2))=>
      independentMixedTest d h k hs ks hp hV σ K _
        (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _) zD zR x))

end Ostmann.Arithmetic.HistoryBulkResidueRootAverage

end

end OAI
