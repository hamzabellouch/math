import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.StringSumProduct
import OAI.Combinatorics.Chromatic.GradedAlgebra.EnergyLimit
import OAI.Combinatorics.Chromatic.Walls.StringRay

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {A B I : Type*} [Fintype I] [DecidableEq I]
variable (a : A→ℕ) (b : B→ℕ) (da : A→(I→ℕ)) (db : B→(I→ℕ))
variable (ka : A→ℤ) (kb : B→ℤ)
variable (ha : ∀d,Admissible (stringEnergy a da ka d))
variable (hb : ∀d,Admissible (stringEnergy b db kb d))
variable (D : AddSubmonoid (I→ℕ)) (hda : ∀s,da s∈D) (hdb : ∀s,db s∈D)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)
include hda hdb hiso in
lemma stringSum_push :
    push w LaurentRay.vUnit Ω P (stringSeries (Sum.elim a b) (Sum.elim da db) (Sum.elim ka kb)
      (stringSum_admissible a b da db ka kb ha hb))=
      push w LaurentRay.vUnit Ω P (stringSeries a da ka ha)*
      push w LaurentRay.vUnit Ω P (stringSeries b db kb hb) := by
  rw [←push_convolution]
  congr 1
  funext d
  rw [convolution_of_isotropic_support LaurentRay.vUnit Ω P _ _ (fun d e hd he=>
    hiso d (stringSeries_support a da ka ha D hda d hd)
      e (stringSeries_support b db kb hb D hdb e he))]
  exact stringSum_series a b da db ka kb ha hb d
end
end ElementaryPositivity.UnitSelections

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {A I : Type*} [Fintype I] [DecidableEq I]
variable (a : Option A→ℕ) (dim : Option A→(I→ℕ)) (k : Option A→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)

abbrev noneEmbedding : PUnit.{1} ↪ Option A := ⟨fun _=>none,fun _ _ _=>Subsingleton.elim _ _⟩
abbrev someEmbedding : A ↪ Option A := ⟨some,Option.some_injective _⟩

lemma option_pullback {T : Type*} (f : Option A→T) :
    (fun s:A⊕PUnit.{1}=>f ((Equiv.optionEquivSumPUnit A).symm s))=
      Sum.elim (fun s=>f (some s)) (fun _=>f none) := by
  funext s
  cases s <;> rfl

include hdim hiso in
lemma stringOption_push (h0 : dim none≠0) :
    push w LaurentRay.vUnit Ω P (stringSeries a dim k he)=
      push w LaurentRay.vUnit Ω P
        (stringSeries (fun s=>a (some s)) (fun s=>dim (some s)) (fun s=>k (some s))
          (stringEmbedding_admissible a dim k he someEmbedding))*
      weightedRay LaurentRay.vUnit Ω (WeightedTorusSeries.weight w (dim none)) (P (dim none))
        (PowerSeries.map LaurentRay.atInfinity (indexedUnit (a none) (k none))) := by
  have H:=funext (stringSeries_reindex a dim k he (Equiv.optionEquivSumPUnit A : Option A ≃ A⊕PUnit.{1}).symm)
  let ha:=stringEmbedding_admissible a dim k he someEmbedding
  let hb:=stringEmbedding_admissible a dim k he noneEmbedding
  let hs:=stringSum_admissible (fun s=>a (some s)) (fun _:PUnit.{1}=>a none)
    (fun s=>dim (some s)) (fun _:PUnit.{1}=>dim none)
    (fun s=>k (some s)) (fun _:PUnit.{1}=>k none) ha hb
  have HC:=stringSeries_congr _ _ _
    (stringReindex_admissible (Equiv.optionEquivSumPUnit A : Option A ≃ A⊕PUnit.{1}).symm a dim k he)
    _ _ _ hs (option_pullback a) (option_pullback dim) (option_pullback k)
  rw [←(HC.symm.trans H)]
  have HH:=stringSum_push (fun s=>a (some s)) (fun _:PUnit.{1}=>a none)
    (fun s=>dim (some s)) (fun _:PUnit.{1}=>dim none)
    (fun s=>k (some s)) (fun _:PUnit.{1}=>k none) ha hb D
    (fun s=>hdim (some s)) (fun _=>hdim none) w Ω P hiso
  rw [HH,oneString_push_literal (a none) (dim none) (k none) h0 hb w Ω P]
end
end ElementaryPositivity.UnitSelections

namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I] [IsEmpty S]
variable (a : S→ℕ) (dim : S→(I→ℕ)) (k : S→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)

local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid

omit [DecidableEq I] in
lemma stringEmpty_push : push w LaurentRay.vUnit Ω P (stringSeries a dim k he)=1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero=>
    rw [coeff_zero_eq_constantCoeff,push_constant w LaurentRay.vUnit Ω P _
      (stringSeries_zero a dim k he (fun s=>isEmptyElim s))]
    simp
  | succ n=>
    simp only [push,coeff_mk,pushCoeff,coeff_one,show n+1≠0 from Nat.succ_ne_zero n,ite_false]
    apply Finset.sum_eq_zero
    intro d hd
    have H : d.val≠0 := by
      intro hz
      have HH:=d.property
      rw [hz,map_zero] at HH
      omega
    rw [stringSeries_empty a dim k he d.val H,Torus.monomial_zero]
end
end ElementaryPositivity.UnitSelections

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
universe u
variable {S : Type u} {I : Type*} [Fintype I] [DecidableEq I]
variable (a : S→ℕ) (dim : S→(I→ℕ)) (k : S→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D) (h0 : ∀s,dim s≠0)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)

def stringLiteralUnit (s : S) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  weightedRay LaurentRay.vUnit Ω (WeightedTorusSeries.weight w (dim s)) (P (dim s))
    (PowerSeries.map LaurentRay.atInfinity (indexedUnit (a s) (k s)))

include hdim h0 hiso in
theorem finiteString_literal [Finite S] :
    ∃l : List S,l.Nodup ∧ (∀s,s∈l) ∧
      push w LaurentRay.vUnit Ω P (stringSeries a dim k he)=
        (l.map (stringLiteralUnit a dim k w Ω P)).prod := by
  classical
  revert a dim k
  induction S using Finite.induction_empty_option with
  | @of_equiv A B e ih =>
    intro a dim k he hdim h0
    let heA:=stringReindex_admissible e a dim k he
    obtain ⟨l,hl,hall,H⟩:=ih (fun s=>a (e s)) (fun s=>dim (e s)) (fun s=>k (e s))
      heA (fun s=>hdim (e s)) (fun s=>h0 (e s))
    refine ⟨l.map e,hl.map e.injective,?_,?_⟩
    · intro s
      exact List.mem_map.mpr ⟨e.symm s,hall (e.symm s),e.apply_symm_apply s⟩
    · rw [List.map_map]
      change push w LaurentRay.vUnit Ω P (stringSeries a dim k he) =
        (l.map (stringLiteralUnit (fun s=>a (e s)) (fun s=>dim (e s))
          (fun s=>k (e s)) w Ω P)).prod
      rw [←H]
      congr 1
      exact (funext (stringSeries_reindex a dim k he e)).symm
  | h_empty =>
    intro a dim k he hdim h0
    refine ⟨[],by simp,fun s=>isEmptyElim s,?_⟩
    simpa using stringEmpty_push a dim k he w Ω P
  | @h_option A inst ih =>
    intro a dim k he hdim h0
    let heA:=stringEmbedding_admissible a dim k he someEmbedding
    obtain ⟨l,hl,hall,H⟩:=ih (fun s=>a (some s)) (fun s=>dim (some s)) (fun s=>k (some s))
      heA (fun s=>hdim (some s)) (fun s=>h0 (some s))
    refine ⟨l.map some++[none],?_,?_,?_⟩
    · rw [List.nodup_append]
      refine ⟨hl.map (Option.some_injective _),by simp,?_⟩
      simp
    · intro s
      cases s with
      | none=>simp
      | some s=>simp [hall s]
    · rw [stringOption_push a dim k he D hdim w Ω P hiso (h0 none)]
      rw [H,List.map_append,List.prod_append,List.map_map,List.map_singleton,List.prod_singleton]
      rfl
end
end ElementaryPositivity.UnitSelections

end

end OAI
