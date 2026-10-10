import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.UnitRowSelection

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity
noncomputable section
variable {S : Type*} (a : S → ℕ)

lemma unitRowCount_sum (b : ℕ) (q : Σn,UnitIndex b n) :
    (unitRowCount b q).val.sum (fun _ m=>m)=q.1 := by
  change ((unitRowSelection b q).val).toFinsupp.sum (fun _ m=>m)=q.1
  exact (Multiset.toFinsupp_sum_eq _).trans (unitRowSelection_card b q.1 q.2)

lemma unitRowCount_zero_iff (b : ℕ) (q : Σn,UnitIndex b n) :
    (unitRowCount b q).val=0 ↔ q.1=0 := by
  constructor
  · intro h
    rw [←unitRowCount_sum b q,h,Finsupp.sum_zero_index]
  · intro h
    change ((unitRowSelection b q).val).toFinsupp=0
    have hm : (unitRowSelection b q).val=0 := by
      apply Multiset.card_eq_zero.mp
      rw [unitRowSelection_card,h]
    rw [hm,Multiset.toFinsupp_zero]

abbrev SupportedUnitRows := {r : ∀s,Σn,UnitIndex (a s) n //
  (Function.support (fun s=>(unitRowCount (a s) (r s)).val)).Finite}

lemma supportedRows_finite_nonempty (r : SupportedUnitRows a) :
    {s | (r.val s).1≠0}.Finite := by
  have he : {s | (r.val s).1≠0}=Function.support (fun s=>(unitRowCount (a s) (r.val s)).val) := by
    ext s
    exact not_congr (unitRowCount_zero_iff (a s) (r.val s)).symm
  rw [he]
  exact r.property

def columnRow (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) (s : S) :
    CountSelection (fun _ : ℕ=>a s≠0) :=
  ⟨f.val.curry s,fun j h=>f.property (s,j) h⟩

def columnRows (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) : SupportedUnitRows a :=
  ⟨fun s=>(unitRowCount (a s)).symm (columnRow a f s),by
    have he : (fun s=>(unitRowCount (a s)
        ((unitRowCount (a s)).symm (columnRow a f s))).val)=f.val.curry := by
      funext s
      rw [Equiv.apply_symm_apply]
      rfl
    rw [he]
    exact Finsupp.hasFiniteSupport f.val.curry⟩

def rowsColumn (r : SupportedUnitRows a) : CountSelection (fun u : S×ℕ=>a u.1≠0) :=
  ⟨(Finsupp.ofSupportFinite (fun s=>(unitRowCount (a s) (r.val s)).val) r.property).uncurry,
    fun u h=>(unitRowCount (a u.1) (r.val u.1)).property u.2 h⟩

def allUnitRowsEquiv : CountSelection (fun u : S×ℕ=>a u.1≠0) ≃ SupportedUnitRows a where
  toFun:=columnRows a
  invFun:=rowsColumn a
  left_inv f:=by
    apply Subtype.ext
    ext u
    change ((unitRowCount (a u.1)) ((unitRowCount (a u.1)).symm (columnRow a f u.1))).val u.2=f.val u
    rw [Equiv.apply_symm_apply]
    rfl
  right_inv r:=by
    apply Subtype.ext
    funext s
    apply (unitRowCount (a s)).injective
    change (unitRowCount (a s)) ((unitRowCount (a s)).symm (columnRow a (rowsColumn a r) s))=_
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    ext j
    rfl

lemma allUnitRows_count (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) (s : S) :
    (unitRowCount (a s) ((allUnitRowsEquiv a f).val s)).val=f.val.curry s := by
  change (unitRowCount (a s) ((unitRowCount (a s)).symm (columnRow a f s))).val=_
  rw [Equiv.apply_symm_apply]
  rfl

lemma allUnitRows_energy (k : S → ℤ) (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) :
    f.val.sum (fun u m=>m • (k u.1-2*(u.2:ℤ)))=
      f.val.curry.sum (fun s _=>unitEnergy (a s)
        ((allUnitRowsEquiv a f).val s).1 (k s) ((allUnitRowsEquiv a f).val s).2) := by
  rw [←Finsupp.sum_curry_index f.val (fun s j m=>m • (k s-2*(j:ℤ)))]
  apply Finset.sum_congr rfl
  intro s _
  rw [←allUnitRows_count a f s]
  exact unitRowCount_energy (a s) ((allUnitRowsEquiv a f).val s).1 (k s) ((allUnitRowsEquiv a f).val s).2

lemma allUnitRows_dimension {T : Type*} [AddCommMonoid T] (dim : S → T)
    (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) :
    f.val.sum (fun u m=>m • dim u.1)=
      f.val.curry.sum (fun s _=>((allUnitRowsEquiv a f).val s).1 • dim s) := by
  rw [←Finsupp.sum_curry_index f.val (fun s _ m=>m • dim s)]
  apply Finset.sum_congr rfl
  intro s _
  rw [←allUnitRows_count a f s]
  change (∑j∈(unitRowCount (a s) ((allUnitRowsEquiv a f).val s)).val.support,
    (unitRowCount (a s) ((allUnitRowsEquiv a f).val s)).val j • dim s)=_
  rw [←Finset.sum_smul]
  congr 1
  exact unitRowCount_sum (a s) ((allUnitRowsEquiv a f).val s)

def rowFinsupp (r : SupportedUnitRows a) : S →₀ ℕ →₀ ℕ :=
  Finsupp.ofSupportFinite (fun s=>(unitRowCount (a s) (r.val s)).val) r.property

lemma rowFinsupp_equiv (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) :
    rowFinsupp a (allUnitRowsEquiv a f)=f.val.curry := by
  ext s j
  exact congrArg (fun r : ℕ →₀ ℕ=>r j) (allUnitRows_count a f s)

def rowsDimension {T : Type*} [AddCommMonoid T] (dim : S → T) (r : SupportedUnitRows a) : T :=
  (rowFinsupp a r).sum (fun s _=>(r.val s).1 • dim s)

def rowsEnergy (k : S → ℤ) (r : SupportedUnitRows a) : ℤ :=
  (rowFinsupp a r).sum (fun s _=>unitEnergy (a s) (r.val s).1 (k s) (r.val s).2)

lemma rowsDimension_equiv {T : Type*} [AddCommMonoid T] (dim : S → T)
    (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) :
    rowsDimension a dim (allUnitRowsEquiv a f)=f.val.sum (fun u m=>m • dim u.1) := by
  rw [rowsDimension,rowFinsupp_equiv]
  exact (allUnitRows_dimension a dim f).symm

lemma rowsEnergy_equiv (k : S → ℤ) (f : CountSelection (fun u : S×ℕ=>a u.1≠0)) :
    rowsEnergy a k (allUnitRowsEquiv a f)=f.val.sum (fun u m=>m • (k u.1-2*(u.2:ℤ))) := by
  rw [rowsEnergy,rowFinsupp_equiv]
  exact (allUnitRows_energy a k f).symm

end
end ElementaryPositivity.UnitSelections
end
end

end OAI
