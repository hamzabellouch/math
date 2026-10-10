import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.HNThreshold
import OAI.Combinatorics.Chromatic.QuantumTorus.StringStripDimension

namespace OAI

section
namespace ElementaryPositivity.SignedMultiplicity
open RawShuffle EnergyLaurent
noncomputable section
variable {A B I : Type*} [Fintype I] [DecidableEq I]
variable (ea : A → Prop) (eb : B → Prop) (da : A → (I→ℕ)) (db : B → (I→ℕ))
variable (ka : A → ℤ) (kb : B → ℤ)

def countSumDimensionEquiv (d : I→ℕ) :
    DimensionCounts (Sum.elim ea eb) (Sum.elim da db) d ≃
      Σs : DimensionSplit d,DimensionCounts ea da s.left × DimensionCounts eb db s.right :=
  ((countSumEquiv ea eb).subtypeEquiv (fun x=>by
    change countDimension _ _ x=d ↔ _
    rw [countDimension,countSum_sum]
    rfl)).trans (dimensionProduct (countDimension ea da) (countDimension eb db) d).symm

omit [Fintype I] [DecidableEq I] in
lemma countSumDimension_energy (d : I→ℕ)
    (f : DimensionCounts (Sum.elim ea eb) (Sum.elim da db) d) :
    countEnergy (Sum.elim ea eb) (Sum.elim ka kb) f.val=
      countEnergy ea ka (countSumDimensionEquiv ea eb da db d f).2.1.val+
      countEnergy eb kb (countSumDimensionEquiv ea eb da db d f).2.2.val :=
  countSum_sum ea eb f.val (Sum.elim ka kb)

variable (ha : ∀d,Admissible (fun f : DimensionCounts ea da d=>countEnergy ea ka f.val))
variable (hb : ∀d,Admissible (fun f : DimensionCounts eb db d=>countEnergy eb kb f.val))

include ha hb in
lemma countSum_admissible (d : I→ℕ) :
    Admissible (fun f : DimensionCounts (Sum.elim ea eb) (Sum.elim da db) d=>
      countEnergy (Sum.elim ea eb) (Sum.elim ka kb) f.val) := by
  let k (s : DimensionSplit d) (f : DimensionCounts ea da s.left × DimensionCounts eb db s.right) :=
    countEnergy ea ka f.1.val+countEnergy eb kb f.2.val
  exact admissible_injective (admissible_sigma k (fun s=>admissible_prod (ha s.left) (hb s.right)))
    (countSumDimensionEquiv ea eb da db d) (countSumDimensionEquiv ea eb da db d).injective
    (fun f=>(countSumDimension_energy ea eb da db ka kb d f).symm)

lemma countSum_series (d : I→ℕ) :
    series _ (countSum_admissible ea eb da db ka kb ha hb d)=
      ∑s : DimensionSplit d,series _ (ha s.left)*series _ (hb s.right) := by
  let k (s : DimensionSplit d) (f : DimensionCounts ea da s.left × DimensionCounts eb db s.right) :=
    countEnergy ea ka f.1.val+countEnergy eb kb f.2.val
  rw [series_equiv _ (admissible_sigma k (fun s=>admissible_prod (ha s.left) (hb s.right)))
    (countSumDimensionEquiv ea eb da db d) (fun f=>(countSumDimension_energy ea eb da db ka kb d f).symm),
    series_sigma]
  apply Finset.sum_congr rfl
  intro s hs
  exact (series_mul (ha s.left) (hb s.right)).symm
end
end ElementaryPositivity.SignedMultiplicity

end
section
namespace ElementaryPositivity.SignedMultiplicity
open EnergyLaurent
noncomputable section
variable {A B I : Type*} (e : A ≃ B) (even : B→Prop) (dim : B→(I→ℕ)) (k : B→ℤ)

def dimensionReindex (d : I→ℕ) : DimensionCounts (fun a=>even (e a)) (fun a=>dim (e a)) d ≃
    DimensionCounts even dim d :=
  (countReindex e _ _ (fun _=>Iff.rfl)).subtypeEquiv (fun f=>by
    change f.val.sum (fun a n=>n • dim (e a))=d ↔ _
    change _ ↔ (countReindex e _ _ (fun _=>Iff.rfl) f).val.sum (fun b n=>n • dim b)=d
    rw [countReindex_sum])

lemma dimensionReindex_energy (d : I→ℕ)
    (f : DimensionCounts (fun a=>even (e a)) (fun a=>dim (e a)) d) :
    countEnergy even k (dimensionReindex e even dim d f).val=
      countEnergy (fun a=>even (e a)) (fun a=>k (e a)) f.val :=
  countReindex_sum e _ _ (fun _=>Iff.rfl) f.val k

variable (he : ∀d,Admissible (fun f : DimensionCounts even dim d=>countEnergy even k f.val))
include he in
lemma dimensionReindex_admissible (d : I→ℕ) :
    Admissible (fun f : DimensionCounts (fun a=>even (e a)) (fun a=>dim (e a)) d=>
      countEnergy _ (fun a=>k (e a)) f.val) :=
  admissible_injective (he d) (dimensionReindex e even dim d)
    (dimensionReindex e even dim d).injective (dimensionReindex_energy e even dim k d)

lemma dimensionReindex_series (d : I→ℕ) :
    series _ (dimensionReindex_admissible e even dim k he d)=series _ (he d) :=
  series_equiv _ _ (dimensionReindex e even dim d) (dimensionReindex_energy e even dim k d)
end
end ElementaryPositivity.SignedMultiplicity

namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent
noncomputable section
variable {S T I : Type*} (e : S ≃ T) (a : T→ℕ) (dim : T→(I→ℕ)) (k : T→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))

def stringReindex (d : I→ℕ) :
    StringCounts (fun s=>a (e s)) (fun s=>dim (e s)) d ≃ StringCounts a dim d :=
  dimensionReindex (Equiv.prodCongr e (Equiv.refl ℕ)) (fun x=>a x.1≠0) (fun x=>dim x.1) d

lemma stringReindex_energy (d : I→ℕ)
    (f : StringCounts (fun s=>a (e s)) (fun s=>dim (e s)) d) :
    stringEnergy a dim k d (stringReindex e a dim d f)=
      stringEnergy (fun s=>a (e s)) (fun s=>dim (e s)) (fun s=>k (e s)) d f :=
  dimensionReindex_energy (Equiv.prodCongr e (Equiv.refl ℕ))
    (fun x=>a x.1≠0) (fun x=>dim x.1) (fun x=>k x.1-2*(x.2:ℤ)) d f

include he in
lemma stringReindex_admissible (d : I→ℕ) :
    Admissible (stringEnergy (fun s=>a (e s)) (fun s=>dim (e s)) (fun s=>k (e s)) d) :=
  admissible_injective (he d) (stringReindex e a dim d) (stringReindex e a dim d).injective
    (stringReindex_energy e a dim k d)
end
end ElementaryPositivity.UnitSelections

end

end OAI
