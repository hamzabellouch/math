import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceCanonicalPair

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

def reindexedCanonicalWeight (k j : ℕ)
    (B V : (j:ℕ) → State k (j+1) → ℤ) (R : ℕ → Finset ℕ+)
    (leafMask : ℤ → State k 0 → Prop) (X Δ W : ℝ)
    (hL hR : CopiedState k j) (y : OutsideState k j)
    (s v w : ℤ) (tL tR : HistoryReconstruction.Tree j) : ℂ :=
  let q := reconstructedPivot k j (pairedState k j hL hR y) s v w
  if hp:0<q then
    if s≠0 ∧ positivePivotOfPos q hp∈R j ∧ s*q=v*(∏i,hR i)-w*(∏i,hL i) then
      retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
        X Δ W j v (sourceState k j q hL y) tL *
      conj (retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
        X Δ W j w (sourceState k j q hR y) tR)
    else 0
  else 0

theorem reindexedCanonicalWeight_eq (k j : ℕ) (hj:j<k)
    (B V : (j:ℕ) → State k (j+1) → ℤ) (R : ℕ → Finset ℕ+)
    (leafMask : ℤ → State k 0 → Prop) (X Δ W : ℝ)
    (hL hR : CopiedState k j) (y : OutsideState k j)
    (s v w : ℤ) (tL tR : HistoryReconstruction.Tree j)
    (hlarge : ∀i,∀q:ℕ,Nat.Prime q → q∣(pairedState k j hL hR y i).natAbs → s.natAbs<q)
    (hPB : ∀P∈R j,(P:ℤ)≤B j (pairedState k j hL hR y))
    (hv : |v|≤V j (pairedState k j hL hR y))
    (hw : |w|≤V j (pairedState k j hL hR y))
    (hgap : 2*B j (pairedState k j hL hR y)*V j (pairedState k j hL hR y)<∏i,hR i) :
    reindexedCanonicalWeight k j B V R leafMask X Δ W hL hR y s v w tL tR =
      retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
        X Δ W (j+1) s (pairedState k j hL hR y) ((v,w),tL,tR) := by
  let x := pairedState k j hL hR y
  let q := reconstructedPivot k j x s v w
  let A := retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
    X Δ W j v (sourceState k j q hL y) tL
  let C := retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
    X Δ W j w (sourceState k j q hR y) tR
  have hsucc : retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
      X Δ W (j+1) s x ((v,w),tL,tR) =
      if localTransferSupport k j B V (canonicalHistoryExtra k R) s x ((v,w),tL,tR) then A*conj C else 0 := by
    rw [retainedHistoryWeight_succ]
    simp only [canonicalHistoryMask_succ,and_true]
    rfl
  have hguard (hz : retainedHistoryWeight k B V (canonicalHistoryExtra k R) (canonicalHistoryMask k leafMask)
      X Δ W (j+1) s x ((v,w),tL,tR)≠0) :
      ∃hp:0<q,s≠0 ∧ positivePivotOfPos q hp∈R j ∧ s*q=v*(∏i,hR i)-w*(∏i,hL i) := by
    have hs := retainedHistoryWeight_support hz
    have hext := hs.2.2.2.1
    obtain ⟨hp,hpr⟩ := (canonicalHistoryExtra_succ_iff k j R s x ((v,w),tL,tR)).mp hext
    refine ⟨hp,hs.1.root_ne_zero,hpr,?_⟩
    exact Int.mul_ediv_cancel' hs.2.1.integral
  change (if hp:0<q then if s≠0 ∧ positivePivotOfPos q hp∈R j ∧
    s*q=v*(∏i,hR i)-w*(∏i,hL i) then A*conj C else 0 else 0)=_
  by_cases hp:0<q
  · rw [dite_eq_left hp]
    by_cases hg:s≠0 ∧ positivePivotOfPos q hp∈R j ∧ s*q=v*(∏i,hR i)-w*(∏i,hL i)
    · rw [ite_eq_left hg]
      by_cases ha:A=0
      · rw [hsucc,ha]
        simp only [zero_mul,ite_self]
      by_cases hc:C=0
      · rw [hsucc,hc]
        simp only [map_zero,mul_zero,ite_self]
      have hl := (retainedHistoryWeight_support ha).current
      have hr := (retainedHistoryWeight_support hc).current
      have hn := hl.paired_of_reversal_prime_factors hj hr hg.1 hg.2.2.symm hlarge
      have hq : ((positivePivotOfPos q hp:ℕ+):ℤ)=q := Int.toNat_of_nonneg hp.le
      have hnode := nodeSupports_pairedState_of_reversal hj hl hr hn hg.2.2.symm
        (by simpa only [hq] using hPB _ hg.2.1) hv hw hgap
      have hex : canonicalHistoryExtra k R (j+1) s x ((v,w),tL,tR) :=
        ⟨positivePivotOfPos q hp,hg.2.1,hq.symm⟩
      rw [hsucc,ite_eq_left ⟨hn,hnode.1,hnode.2,hex⟩]
    · rw [ite_eq_right hg]
      symm
      by_contra hz
      obtain ⟨hp',hgg⟩ := hguard hz
      exact hg hgg
  · rw [dite_eq_right hp]
    symm
    by_contra hz
    exact hp (hguard hz).choose

end Ostmann.Characters.Template

end

end OAI
