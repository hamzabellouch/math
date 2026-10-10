import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSupportBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateCompositePivotSupportSampled

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem sampled_outside_coprime_iff {k J j Q : ℕ} (width : Role → ℕ)
    (p : (schedule k J).Constituent width → PrimeUpTo Q)
    (o : SampleOrigins k (j+1) (schedule k J).Slot) (P : ℤ) :
    (∀ i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i},
      IsCoprime P (constituentSampleState (schedule k J) width p (o.outside i))) ↔
    (∀ (i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i})
      (a : Fin (width ((schedule k J).role (o.outside i)))),
        IsCoprime ((p ⟨o.outside i,a⟩).val : ℤ) P) := by
  simp only [constituentSampleState, IsCoprime.prod_right_iff, Finset.mem_univ, forall_true_left]
  exact forall_congr' (fun i => forall_congr' (fun a => isCoprime_comm))

theorem primeSample_pairwise_of_injective {k j Q : ℕ} (width : Role → ℕ)
    (p : (schedule k j).Constituent width → PrimeUpTo Q)
    (hinj : Function.Injective (fun i => (p i).val)) :
    Pairwise (fun i h => IsCoprime
      (constituentSampleState (schedule k j) width p i)
      (constituentSampleState (schedule k j) width p h)) := by
  apply (constituent_prime_support_iff (schedule k j) width p).mp _ |>.1
  intro i h hne
  exact (Nat.coprime_primes (primeUpTo_prime (p i)) (primeUpTo_prime (p h))).mpr
    (fun he => hne (hinj he))

theorem prime_transferSupport_iff_sampled {k Q : ℕ}
    (B V : (j : ℕ) → State k (j+1) → ℤ)
    (extra : (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (j : ℕ) (hj : j ≤ k) (s : ℤ) (width : Role → ℕ)
    (p : (schedule k j).Constituent width → PrimeUpTo Q)
    (hinj : Function.Injective (fun i => (p i).val)) (t : HistoryReconstruction.Tree j) :
    TransferSupport k B V extra j s (constituentSampleState (schedule k j) width p) t ↔
      SampledTransferSupport k (constituentSampleState (schedule k j) width p) B V extra j
        (SampleOrigins.root k j) s (constituentSampleState (schedule k j) width p) t :=
  transferSupport_iff_sampled B V extra j hj s _ t
    (primeSample_pairwise_of_injective width p hinj)

theorem prime_transferSupport_indicator {k Q : ℕ}
    (B V : (j : ℕ) → State k (j+1) → ℤ)
    (extra : (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (j : ℕ) (hj : j ≤ k) (s : ℤ) (width : Role → ℕ)
    (p : (schedule k j).Constituent width → PrimeUpTo Q) (t : HistoryReconstruction.Tree j)
    (z : ℂ) :
    (if Pairwise (fun i h => (p i).val.Coprime (p h).val) then
      if TransferSupport k B V extra j s (constituentSampleState (schedule k j) width p) t
        then z else 0 else 0) =
    (if Pairwise (fun i h => (p i).val.Coprime (p h).val) then
      if SampledTransferSupport k (constituentSampleState (schedule k j) width p) B V extra j
        (SampleOrigins.root k j) s (constituentSampleState (schedule k j) width p) t
        then z else 0 else 0) := by
  by_cases hp : Pairwise (fun i h => (p i).val.Coprime (p h).val)
  · simp only [ite_eq_left hp]
    rw [transferSupport_iff_sampled B V extra j hj s _ t
      ((constituent_prime_support_iff (schedule k j) width p).mp hp).1]
  · simp only [ite_eq_right hp]

end Ostmann.Characters.Template

end

end OAI
