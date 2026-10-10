import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinPointwise

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
attribute [local instance] Classical.propDecidable

def twoPrimeSample {I : Type*} [DecidableEq I] {A : ℕ}
    (p : I→PrimeUpTo A) (L S : I) (q r : PrimeUpTo A) : I→PrimeUpTo A :=
  Function.update (Function.update p L q) S r

@[simp] theorem twoPrimeSample_val {I : Type*} [DecidableEq I] {A : ℕ}
    (p : I→PrimeUpTo A) (L S : I) (q r : PrimeUpTo A) (i : I) :
    (twoPrimeSample p L S q r i).val=twoPrimeAssignment (fun i=>(p i).val) L S q.val r.val i := by
  by_cases hiS : i=S <;> by_cases hiL : i=L <;>
    simp_all [twoPrimeSample,twoPrimeAssignment]

theorem twoPrimeSample_prime {I : Type*} [DecidableEq I] {A : ℕ}
    (p : I→PrimeUpTo A) (L S : I) (q r : PrimeUpTo A) (i : I) :
    (twoPrimeAssignment (fun i=>(p i).val) L S q.val r.val i).Prime := by
  rw [←twoPrimeSample_val p L S q r i]
  exact primeUpTo_prime _

def sourceRetainedPairAt {k A : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ) (a : (q:ℕ)→ZMod q)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) A)
    (p : SurvivingPrimeIndex k j (sourceWidth cfg m)→PrimeUpTo A)
    (L S : SurvivingPrimeIndex k j (sourceWidth cfg m)) (q r : PrimeUpTo A)
    (P : ℕ+) (s : ℤ) (t u : HistoryReconstruction.Tree j) : ℂ :=
  let x := twoPrimeSample p L S q r
  let χd := scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData (Q:=A) cfg m (fun _=>χ)) j
  let ad := scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData (Q:=A) cfg m (fun _=>a)) j
  unitRetainedPhase k j hj (sourceWidth cfg m) ζ χd ad (fun i=>x (.inl (σ.symm i)))
    (fun i=>x (.inr i)) P s t *
  conj (unitRetainedPhase k j hj (sourceWidth cfg m) ζ χd ad (fun i=>x (.inl (ρ.symm i)))
    (fun i=>x (.inr i)) P s u)

theorem sourceRetainedPairAt_eq {k A : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ) (a : (q:ℕ)→ZMod q)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) A)
    (p : SurvivingPrimeIndex k j (sourceWidth cfg m)→PrimeUpTo A)
    (L S : SurvivingPrimeIndex k j (sourceWidth cfg m)) (q r : PrimeUpTo A)
    (hc : Pairwise (fun i v=>(twoPrimeAssignment (fun i=>(p i).val) L S q.val r.val i).Coprime
      (twoPrimeAssignment (fun i=>(p i).val) L S q.val r.val v)))
    (P : ℕ+) (s : ℤ) (t u : HistoryReconstruction.Tree j) :
    let χd := scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData (Q:=A) cfg m (fun _=>χ)) j
    let ad := scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData (Q:=A) cfg m (fun _=>a)) j
    letI : ∀i,Fact (twoPrimeAssignment (fun i=>(p i).val) L S q.val r.val i).Prime :=
      fun i=>⟨twoPrimeSample_prime p L S q r i⟩
    sourceRetainedPairAt cfg m j hj σ ρ χ a ζ p L S q r P s t u =
      survivingPhasePair k j hj (sourceWidth cfg m)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ)
        (twoPrimeAssignment (fun i=>(p i).val) L S q.val r.val)
        (finiteSurvivingCharacters k j hj (sourceWidth cfg m) χd)
        (finiteSurvivingTranslations k j hj (sourceWidth cfg m) ad)
        (finiteSurvivingUnits k j hj (sourceWidth cfg m) ζ) P s t u := by
  let x := twoPrimeSample p L S q r
  have hx : Sum.elim (fun i=>x (.inl i)) (fun i=>x (.inr i))=x := by
    funext i
    cases i <;> rfl
  have hcp : Pairwise (fun i v=>(Sum.elim (fun i=>x (.inl i)) (fun i=>x (.inr i)) i).val.Coprime
      (Sum.elim (fun i=>x (.inl i)) (fun i=>x (.inr i)) v).val) := by
    simpa only [hx,x,twoPrimeSample_val] using hc
  have he := source_unitRetainedPhase_pair cfg m j hj ζ χ a σ ρ
    (fun i=>x (.inl i)) (fun i=>x (.inr i)) hcp P s t u
  have hv : (fun i=>(Sum.elim (fun i=>x (.inl i)) (fun i=>x (.inr i)) i).val)=
      twoPrimeAssignment (fun i=>(p i).val) L S q.val r.val := by
    funext i
    rw [hx,twoPrimeSample_val]
  simpa only [hv,sourceRetainedPairAt,x] using he

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
