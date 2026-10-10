import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinData

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem priorJoinUnary_norms (D : I→I→ℤ) (p : I→ℕ)
    (χ : I→(q:ℕ)→MulChar (ZMod q) ℂ) (ν masks : I→ℕ→ℂ)
    (hm : ∀i q,‖masks i q‖≤1) (L S : I) (q r : ℕ)
    (hlong : ‖indexedLongUnary D p χ ν L S q‖≤1)
    (hshort : ‖indexedShortUnary D p χ ν L S r‖≤1) :
    ‖priorJoinLongUnary D p χ ν masks L S q‖≤1 ∧
    ‖priorJoinShortUnary D p χ ν masks L S r‖≤1 := by
  have mul_bound {a b : ℂ} (ha : ‖a‖≤1) (hb : ‖b‖≤1) : ‖a*b‖≤1 := by
    rw [norm_mul]
    exact (mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  constructor
  · exact mul_bound (mul_bound (longPrimeSupportMask_norm_le p L S q)
      (norm_longCoordinateMask_le masks hm p L S q)) hlong
  · exact mul_bound (mul_bound (shortPrimeSupportMask_norm_le p L S r)
      (norm_shortCoordinateMask_le masks hm S r)) hshort

omit [Fintype I] [DecidableEq I] in

theorem sourceFactors_norms_of_supported {k A V : ℕ}
    (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) A) (hζ : ∀i q,‖ζ i q‖=1)
    (masks : SurvivingPrimeIndex k j (sourceWidth cfg m)→ℕ→ℂ)
    (hm : ∀i q,‖masks i q‖≤1)
    (p : SurvivingPrimeIndex k j (sourceWidth cfg m)→PrimeUpTo A)
    (L S : SurvivingPrimeIndex k j (sourceWidth cfg m)) (hLS : L≠S) (q r : PrimeUpTo A)
    (hχ : ∀i,2<orderOf (χ (twoPrimeSample p L S q r i).val))
    (hV : ∀i,V<(twoPrimeSample p L S q r i).val)
    (ranges : List Bool→Finset ℤ)
    (hrange : ∀path f,f∈ranges path→f≠0 ∧ f.natAbs≤V)
    (t u : SupportedHistory ranges j []) (hroot : t.val.1=u.val.1) (P : ℕ+) :
    ‖sourceLongFactor cfg m j hj σ ρ χ ζ masks p L S P t.val.1 t.val.2 u.val.2 q.val‖≤1 ∧
    ‖sourceShortFactor cfg m j hj σ ρ χ ζ masks p L S P t.val.1 t.val.2 u.val.2 r.val‖≤1 := by
  let χr := sourceSliceCharacters cfg m j hj A χ
  let ζr := finiteSurvivingUnits k j hj (sourceWidth cfg m) ζ
  let σr := copiedSurvivingPermutation k j (sourceWidth cfg m) σ
  let ρr := copiedSurvivingPermutation k j (sourceWidth cfg m) ρ
  let x := twoPrimeAssignment (fun i=>(p i).val) L S q.val r.val
  have hx (i) : x i=(twoPrimeSample p L S q r i).val :=
    (twoPrimeSample_val p L S q r i).symm
  let : ∀i,Fact (x i).Prime := fun i=>⟨hx i ▸ primeUpTo_prime (twoPrimeSample p L S q r i)⟩
  have hχr (i) : χr i (x i)≠1 := by
    have ho : 2<orderOf (χr i (x i)) := by
      rw [hx,show χr=sourceSliceCharacters cfg m j hj A χ from rfl,
        sourceSliceCharacters,finiteSurvivingCharacters,extendCharacterData_prime,
        scheduled_sourceCharacterData_order]
      exact hχ i
    intro he
    rw [he,orderOf_one] at ho
    norm_num at ho
  have ht (i) : HistoryFrequencyUnits (x i) j t.val.1 t.val.2 :=
    historyFrequencyUnits_of_prime_gt_cutoff ranges hrange ((hx i).symm ▸ hV i) [] t
  have hu (i) : HistoryFrequencyUnits (x i) j t.val.1 u.val.2 := by
    rw [hroot]
    exact historyFrequencyUnits_of_prime_gt_cutoff ranges hrange ((hx i).symm ▸ hV i) [] u
  have hn := survivingPhasePair_twoPrimeAssignment_unary_norms k j hj (sourceWidth cfg m)
    σr ρr (fun i=>(p i).val) L S hLS q.val r.val χr hχr ζr
    (fun i v=>(finiteSurvivingUnits_norm k j hj (sourceWidth cfg m) ζ hζ i v).le)
    P t.val.1 t.val.2 u.val.2 ht hu
  exact priorJoinUnary_norms _ _ χr _ masks hm L S q.val r.val hn.1 hn.2

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
