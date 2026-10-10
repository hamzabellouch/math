import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWeight
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurvivingPairwise

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportSurviving
open Template Preliminaries
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sourceState_transferSupport_iff_sampled {k j : ℕ} (hj : j≤k)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (s P : ℤ) (h : CopiedState k j) (y : OutsideState k j)
    (t : HistoryReconstruction.Tree j)
    (hpairs : Pairwise (fun i v=>IsCoprime (sourceState k j P h y i) (sourceState k j P h y v))) :
    TransferSupport k B V extra j s (sourceState k j P h y) t ↔
      SampledTransferSupport k (Sum.elim h y) B V extra j (origins k j) s
        (sourceState k j P h y) t :=
  (transferSupport_iff_reduced B V extra j hj s _ t hpairs).trans
    (reducedTransferSupport_iff_sampled k _ B V extra j (origins k j) s _ t
      (origins_matches k j P h y))

def pivotPrimeGuard {k j Q : ℕ} (width : Role→ℕ) (P : ℕ+)
    (p : SurvivingPrimeIndex k j width→PrimeUpTo Q) : Prop :=
  ∀i,(p i).val.Coprime P

theorem pivotPrimeGuard_of_transferSupport {k j Q : ℕ} (hj : j<k)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (s : ℤ) (P : ℕ+) (width : Role→ℕ)
    (p : SurvivingPrimeIndex k j width→PrimeUpTo Q) (t : HistoryReconstruction.Tree j)
    (hs : TransferSupport k B V extra j s
      (sourceState k j P (copiedSampleState (schedule k j) j width (fun i=>p (.inl i)))
        (outsideSampleState (schedule k j) j width (fun i=>p (.inr i)))) t) :
    pivotPrimeGuard width P p := by
  intro i
  cases i with
  | inl i => exact copiedSample_pivot_coprime hj width hs.current i
  | inr i => exact outsideSample_pivot_coprime hj width hs.current i

theorem prime_transferSupport_iff_sampled {k j Q : ℕ} (hj : j<k)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (s : ℤ) (P : ℕ+) (width : Role→ℕ)
    (p : SurvivingPrimeIndex k j width→PrimeUpTo Q) (t : HistoryReconstruction.Tree j)
    (hpairs : Pairwise (fun i v=>(p i).val.Coprime (p v).val))
    (hpivot : pivotPrimeGuard width P p) :
    TransferSupport k B V extra j s
      (sourceState k j P (copiedSampleState (schedule k j) j width (fun i=>p (.inl i)))
        (outsideSampleState (schedule k j) j width (fun i=>p (.inr i)))) t ↔
    SampledTransferSupport k
      (Sum.elim (copiedSampleState (schedule k j) j width (fun i=>p (.inl i)))
        (outsideSampleState (schedule k j) j width (fun i=>p (.inr i))))
      B V extra j (origins k j) s
      (sourceState k j P (copiedSampleState (schedule k j) j width (fun i=>p (.inl i)))
        (outsideSampleState (schedule k j) j width (fun i=>p (.inr i)))) t :=
  sourceState_transferSupport_iff_sampled hj.le B V extra s P _ _ t
    (prime_sourceState_pairwise hj width P p hpairs hpivot)

theorem prime_transferSupport_iff_guarded_sampled {k j Q : ℕ} (hj : j<k)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (s : ℤ) (P : ℕ+) (width : Role→ℕ)
    (p : SurvivingPrimeIndex k j width→PrimeUpTo Q) (t : HistoryReconstruction.Tree j)
    (hpairs : Pairwise (fun i v=>(p i).val.Coprime (p v).val)) :
    TransferSupport k B V extra j s
      (sourceState k j P (copiedSampleState (schedule k j) j width (fun i=>p (.inl i)))
        (outsideSampleState (schedule k j) j width (fun i=>p (.inr i)))) t ↔
    pivotPrimeGuard width P p ∧ SampledTransferSupport k
      (Sum.elim (copiedSampleState (schedule k j) j width (fun i=>p (.inl i)))
        (outsideSampleState (schedule k j) j width (fun i=>p (.inr i))))
      B V extra j (origins k j) s
      (sourceState k j P (copiedSampleState (schedule k j) j width (fun i=>p (.inl i)))
        (outsideSampleState (schedule k j) j width (fun i=>p (.inr i)))) t := by
  constructor
  · intro hs
    have hp := pivotPrimeGuard_of_transferSupport hj B V extra s P width p t hs
    exact ⟨hp,(prime_transferSupport_iff_sampled hj B V extra s P width p t hpairs hp).mp hs⟩
  · rintro ⟨hp,hs⟩
    exact (prime_transferSupport_iff_sampled hj B V extra s P width p t hpairs hp).mpr hs

theorem retainedWeight_eq_guarded_sampled {k j Q : ℕ} (hj : j<k)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask : (l:ℕ)→ℤ→State k l→Prop) (X Δ W : ℝ)
    (s : ℤ) (P : ℕ+) (width : Role→ℕ)
    (p : SurvivingPrimeIndex k j width→PrimeUpTo Q) (t : HistoryReconstruction.Tree j)
    (hpairs : Pairwise (fun i v=>(p i).val.Coprime (p v).val)) :
    let x := sourceState k j P (copiedSampleState (schedule k j) j width (fun i=>p (.inl i)))
      (outsideSampleState (schedule k j) j width (fun i=>p (.inr i)))
    retainedHistoryWeight k B V extra mask X Δ W j s x t =
    if pivotPrimeGuard width P p ∧ SampledTransferSupport k
      (Sum.elim (copiedSampleState (schedule k j) j width (fun i=>p (.inl i)))
        (outsideSampleState (schedule k j) j width (fun i=>p (.inr i))))
      B V extra j (origins k j) s x t then weight k mask X Δ W j s x t else 0 := by
  dsimp only
  rw [retainedHistoryWeight,prime_transferSupport_iff_guarded_sampled hj B V extra s P width p t hpairs]
  split_ifs <;> rfl

end Ostmann.Characters.TemplateOneSidedSupportSurviving

end

end OAI
