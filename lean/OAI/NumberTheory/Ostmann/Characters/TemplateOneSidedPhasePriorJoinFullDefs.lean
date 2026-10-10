import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinFullSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable

def counterpartSourceMask {I Y : Type*} {A : ℕ} (E : I→Finset (PrimeUpTo A))
    (e : Equiv.Perm I) : I⊕Y→ℕ→ℂ
  | .inl i,q => coordinateMembershipMask E e.symm i q
  | .inr _,_ => 1

theorem counterpartSourceMask_norm {I Y : Type*} {A : ℕ}
    (E : I→Finset (PrimeUpTo A)) (e : Equiv.Perm I) (i : I⊕Y) (q : ℕ) :
    ‖counterpartSourceMask E e i q‖≤1 := by
  cases i with
  | inl i => exact norm_coordinateMembershipMask_le E e.symm i q
  | inr i => exact le_of_eq norm_one

theorem counterpartSourceMask_product {I Y : Type*} [Fintype I] [Fintype Y] {A : ℕ}
    (E : I→Finset (PrimeUpTo A)) (e : Equiv.Perm I)
    (f : I→PrimeUpTo A) (y : Y→PrimeUpTo A) :
    (∏i,counterpartSourceMask E e i (Sum.elim f y i).val) =
      ((∏i,if f (e i)∈E i then (1:ℝ) else 0):ℂ) := by
  simp only [Fintype.prod_sum_type,counterpartSourceMask,Sum.elim_inl,
    Finset.prod_const_one,mul_one]
  rw [←Equiv.prod_comp e]
  simp [coordinateMembershipMask_prime]

def sourcePairAmplitude {k A : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (extra : (l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask : (l:ℕ)→ℤ→State k l→Prop) (X Δ W T D : ℝ)
    (P : ℕ+) (e : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (h h' : ℤ×HistoryReconstruction.Tree j)
    (x : SurvivingPrimeIndex k j (sourceWidth cfg m)→PrimeUpTo A) : ℂ :=
  ((Real.exp (T+D)/((∏i,(x (.inl i)).val:ℕ):ℝ)):ℂ) *
    retainedHistoryWeight k B V extra mask X Δ W j h.1
      (sourceState k j P
        (copiedSampleState (schedule k j) j (sourceWidth cfg m) (fun i=>x (.inl i)))
        (outsideSampleState (schedule k j) j (sourceWidth cfg m) (fun i=>x (.inr i)))) h.2 *
    conj (retainedHistoryWeight k B V extra mask X Δ W j h'.1
      (sourceState k j P
        (copiedSampleState (schedule k j) j (sourceWidth cfg m) (fun i=>x (.inl (e i))))
        (outsideSampleState (schedule k j) j (sourceWidth cfg m) (fun i=>x (.inr i)))) h'.2)

@[simp] theorem twoPrimeSample_self {I : Type*} [DecidableEq I] {A : ℕ}
    (p : I→PrimeUpTo A) (L S : I) : twoPrimeSample p L S (p L) (p S)=p := by
  simp only [twoPrimeSample,Function.update_eq_self]

theorem sourceRetainedPairAt_self {k A : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ) (a : (q:ℕ)→ZMod q)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) A)
    (f : CopiedConstituent (schedule k j) j (sourceWidth cfg m)→PrimeUpTo A)
    (y : OutsideConstituent (schedule k j) j (sourceWidth cfg m)→PrimeUpTo A)
    (L S : SurvivingPrimeIndex k j (sourceWidth cfg m))
    (P : ℕ+) (s : ℤ) (t u : HistoryReconstruction.Tree j) :
    let x := Sum.elim f y
    let χd := scheduledCharacterData k (sourceWidth cfg m)
      (sourceCharacterData (Q:=A) cfg m (fun _=>χ)) j
    let ad := scheduledTranslationData k (sourceWidth cfg m)
      (sourceTranslationData (Q:=A) cfg m (fun _=>a)) j
    sourceRetainedPairAt cfg m j hj (Equiv.refl _) e.symm χ a ζ x L S (x L) (x S) P s t u =
      unitRetainedPhase k j hj (sourceWidth cfg m) ζ χd ad f y P s t *
      conj (unitRetainedPhase k j hj (sourceWidth cfg m) ζ χd ad (f∘e) y P s u) := by
  simp only [sourceRetainedPairAt,twoPrimeSample_self,Equiv.refl_symm,Equiv.refl_apply,
    Equiv.symm_symm,Sum.elim_inl,Sum.elim_inr,Function.comp_def]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
