import Mathlib
import OAI.Combinatorics.Chromatic.Walls.StringPositiveFactor

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent RawShuffle WeightedTorusSeries QuantumTorus WallUnits PowerSeries
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : ℕ) (δ : I→ℕ) (k : ℤ)

def oneStringEquiv : (Σn,UnitIndex a n) ≃ CountSelection (fun _ : PUnit×ℕ=>a≠0) :=
  (unitRowCount a).trans (countReindex (Equiv.punitProd ℕ).symm _ _ (fun _=>Iff.rfl))

omit [Fintype I] [DecidableEq I] in
lemma oneString_dimension (q : Σn,UnitIndex a n) :
    countDimension (fun _ : PUnit×ℕ=>a≠0) (fun _=>δ) (oneStringEquiv a q)=q.1 • δ := by
  dsimp only [countDimension,oneStringEquiv,Equiv.trans_apply]
  rw [countReindex_sum]
  change (unitRowCount a q).val.sum (fun _ n=>n • δ)=_
  rw [Finsupp.sum,←Finset.sum_smul]
  change ((unitRowCount a q).val.sum (fun _ n=>n)) • δ=_
  rw [unitRowCount_sum]

lemma oneString_energy (q : Σn,UnitIndex a n) :
    countEnergy (fun _ : PUnit×ℕ=>a≠0) (fun x=>k-2*(x.2:ℤ)) (oneStringEquiv a q)=
      unitEnergy a q.1 k q.2 := by
  dsimp only [countEnergy,oneStringEquiv,Equiv.trans_apply]
  rw [countReindex_sum]
  exact unitRowCount_energy a q.1 k q.2

omit [Fintype I] [DecidableEq I] in
lemma nsmul_dimension_injective (hδ : δ≠0) : Function.Injective (fun n:ℕ=>n • δ) := by
  obtain ⟨i,hi⟩:=Function.ne_iff.mp hδ
  intro n m H
  have HE:=congrArg (fun d:I→ℕ=>d i) H
  change n*δ i=m*δ i at HE
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) HE

variable (hδ : δ≠0)

def unitSigmaFibre (n : ℕ) : UnitIndex a n ≃ {q : Σm,UnitIndex a m // q.1=n} where
  toFun f:=⟨⟨n,f⟩,rfl⟩
  invFun q:=q.property ▸ q.val.2
  left_inv f:=rfl
  right_inv q:=by
    rcases q with ⟨⟨m,f⟩,h⟩
    cases h
    rfl

def oneStringDimensionEquiv (n : ℕ) : UnitIndex a n ≃
    StringCounts (fun _:PUnit=>a) (fun _=>δ) (n • δ) :=
  (unitSigmaFibre a n).trans ((oneStringEquiv a).subtypeEquiv (fun q=>by
    change q.1=n ↔ countDimension _ _ (oneStringEquiv a q)=n • δ
    rw [oneString_dimension]
    exact (nsmul_dimension_injective δ hδ).eq_iff.symm))

variable (he : ∀d,Admissible (stringEnergy (fun _:PUnit=>a) (fun _=>δ) (fun _=>k) d))

omit [Fintype I] [DecidableEq I] in
include hδ in
lemma oneStringSeries_nsmul (n : ℕ) :
    stringSeries (fun _:PUnit=>a) (fun _=>δ) (fun _=>k) he (n • δ)=indexedUnitSeries a n k := by
  symm
  apply series_equiv _ _ (oneStringDimensionEquiv a δ hδ n)
  intro f
  exact oneString_energy a k ⟨n,f⟩

omit [Fintype I] [DecidableEq I] in
lemma oneStringSeries_off (d : I→ℕ) (hd : ∀n:ℕ,n • δ≠d) :
    stringSeries (fun _:PUnit=>a) (fun _=>δ) (fun _=>k) he d=0 := by
  let : IsEmpty (StringCounts (fun _:PUnit=>a) (fun _=>δ) d) := ⟨fun f=>by
    let q:=(oneStringEquiv a).symm f.val
    apply hd q.1
    rw [←oneString_dimension a δ q]
    dsimp only [q]
    rw [Equiv.apply_symm_apply]
    exact f.property⟩
  ext j
  rw [stringSeries,series_coeff]
  simp only [HahnSeries.coeff_zero,Nat.cast_eq_zero]
  exact Nat.card_eq_zero.mpr (Or.inl (inferInstance : IsEmpty _))
end
end ElementaryPositivity.UnitSelections

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : ℕ) (δ : I→ℕ) (k : ℤ) (hδ : δ≠0)
variable (he : ∀d,Admissible (stringEnergy (fun _:PUnit=>a) (fun _=>δ) (fun _=>k) d))
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)

omit [DecidableEq I] in
include hδ in
lemma oneString_push_literal :
    push w LaurentRay.vUnit Ω P (stringSeries (fun _:PUnit=>a) (fun _=>δ) (fun _=>k) he)=
      weightedRay LaurentRay.vUnit Ω (WeightedTorusSeries.weight w δ) (P δ)
        (PowerSeries.map LaurentRay.atInfinity (indexedUnit a k)) := by
  apply push_on_ray
  · intro n
    rw [oneStringSeries_nsmul a δ k hδ he,coeff_map,indexedUnit_literal_expansion]
  · exact oneStringSeries_off a δ k he
end
end ElementaryPositivity.UnitSelections

end

end OAI
