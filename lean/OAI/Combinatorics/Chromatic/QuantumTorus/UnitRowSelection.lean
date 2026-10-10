import Mathlib
import OAI.Combinatorics.Chromatic.Walls.SignedMultiplicity

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity
noncomputable section

def unitSigmaSubtype (a : ℕ) : (Σn,UnitIndex a n) ≃
    {q : Σn,Fin n → ℕ // if a=0 then StrictMono q.2 else Monotone q.2} where
  toFun q:=⟨⟨q.1,q.2.val⟩,q.2.property⟩
  invFun q:=⟨q.val.1,⟨q.val.2,q.property⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

lemma ofFn_signed_iff (a n : ℕ) (f : Fin n → ℕ) :
    (if a=0 then StrictMono f else Monotone f) ↔
      (List.ofFn f).Pairwise (·≤·) ∧
        (List.ofFn f).Pairwise (fun x y=>x=y → a≠0) := by
  rw [List.pairwise_ofFn,List.pairwise_ofFn]
  by_cases h : a=0
  · simp only [ite_eq_left h]
    constructor
    · intro hf
      exact ⟨fun i j hij=>(hf hij).le,fun i j hij he=>False.elim ((hf hij).ne he)⟩
    · rintro ⟨hl,he⟩ i j hij
      exact lt_of_le_of_ne (hl hij) (fun hx=>he hij hx h)
  · simp only [ite_eq_right h]
    constructor
    · intro hf
      exact ⟨fun i j hij=>hf hij.le,fun _ _ _ _=>h⟩
    · rintro ⟨hl,_⟩ i j hij
      rcases hij.eq_or_lt with he|hlt
      · subst j; rfl
      · exact hl hlt

def unitWordEquiv (a : ℕ) : (Σn,UnitIndex a n) ≃ Word (fun _ : ℕ=>a≠0) :=
  (unitSigmaSubtype a).trans
    (List.equivSigmaTuple.symm.subtypeEquiv (fun q=>ofFn_signed_iff a q.1 q.2))

def unitRowSelection (a : ℕ) : (Σn,UnitIndex a n) ≃ Selection (fun _ : ℕ=>a≠0) :=
  (unitWordEquiv a).trans (wordSelectionEquiv _)

def unitRowCount (a : ℕ) : (Σn,UnitIndex a n) ≃ CountSelection (fun _ : ℕ=>a≠0) :=
  (unitWordEquiv a).trans (wordCountEquiv _)

lemma unitRowSelection_val (a n : ℕ) (f : UnitIndex a n) :
    (unitRowSelection a ⟨n,f⟩).val=(List.ofFn f.val:Multiset ℕ) := rfl

lemma unitRowSelection_card (a n : ℕ) (f : UnitIndex a n) :
    (unitRowSelection a ⟨n,f⟩).val.card=n := by
  rw [unitRowSelection_val,Multiset.coe_card,List.length_ofFn]

lemma unitRowSelection_energy (a n : ℕ) (k : ℤ) (f : UnitIndex a n) :
    (((unitRowSelection a ⟨n,f⟩).val).map (fun j:ℕ=>k-2*(j:ℤ))).sum=unitEnergy a n k f := by
  rw [unitRowSelection_val,Multiset.map_coe,Multiset.sum_coe,List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_def,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum,unitEnergy,unitWeight,weight]
end
end ElementaryPositivity.UnitSelections
end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity
noncomputable section

lemma multiset_count_energy {A : Type*} [DecidableEq A] (m : Multiset A) (e : A → ℤ) :
    m.toFinsupp.sum (fun x n=>n • e x)=(m.map e).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
    change (({x}:Multiset A)+m).toFinsupp.sum _=((({x}:Multiset A)+m).map e).sum
    rw [Multiset.toFinsupp_add]
    rw [Finsupp.sum_add_index' (h:=fun x n=>n • e x) (by simp) (by intro a b c; exact add_nsmul (e a) b c)]
    simp only [Multiset.toFinsupp_singleton,Multiset.map_add,Multiset.sum_add,
      Multiset.map_singleton,Multiset.sum_singleton,ih]
    rw [Finsupp.sum_single_index (h:=fun x n=>n • e x) (by simp),one_nsmul]

lemma unitRowCount_energy (a n : ℕ) (k : ℤ) (f : UnitIndex a n) :
    (unitRowCount a ⟨n,f⟩).val.sum (fun j r=>r • (k-2*(j:ℤ)))=unitEnergy a n k f := by
  change ((unitRowSelection a ⟨n,f⟩).val).toFinsupp.sum _=_
  rw [multiset_count_energy,unitRowSelection_energy]

section FiniteRows
variable {S : Type*} [Fintype S] [DecidableEq S]
variable (a : S → ℕ)

abbrev ColumnSelection := {f : (Σ_ : S,ℕ) →₀ ℕ // ∀s j,¬(a s≠0) → f ⟨s,j⟩≤1}

def columnRowEquiv : ColumnSelection a ≃ (∀s,CountSelection (fun _ : ℕ=>a s≠0)) :=
  ((Finsupp.sigmaFinsuppEquivPiFinsupp (ιs:=fun _ : S=>ℕ) (α:=ℕ)).subtypeEquiv
    (fun f=>(show (∀s j,¬(a s≠0) → f ⟨s,j⟩≤1) ↔
      (∀s,∀j,¬(a s≠0) → Finsupp.sigmaFinsuppEquivPiFinsupp f s j≤1) from Iff.rfl))).trans
        (Equiv.subtypePiEquivPi (p:=fun s (f:ℕ→₀ℕ)=>∀j,¬(a s≠0) → f j≤1))

def unitRowsEquiv : (∀s,Σn,UnitIndex (a s) n) ≃ ColumnSelection a :=
  (Equiv.piCongrRight (fun s=>unitRowCount (a s))).trans (columnRowEquiv a).symm

omit [DecidableEq S] in
lemma unitRows_split (f : ∀s,Σn,UnitIndex (a s) n) (s : S) :
    Finsupp.split (unitRowsEquiv a f).val s=(unitRowCount (a s) (f s)).val := by
  change (((columnRowEquiv a) ((columnRowEquiv a).symm
    (fun s=>unitRowCount (a s) (f s)))) s).val=_
  rw [Equiv.apply_symm_apply]

omit [DecidableEq S] in
lemma sigma_sum_univ (f : (Σ_ : S,ℕ) →₀ ℕ) (e : (Σ_ : S,ℕ) → ℤ) :
    f.sum (fun x r=>r • e x)=∑s,(Finsupp.split f s).sum (fun j r=>r • e ⟨s,j⟩) := by
  rw [Finsupp.sigma_sum]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro s _ hs
  have hz : Finsupp.split f s=0 := by
    by_contra hn
    exact hs ((Finsupp.mem_splitSupport_iff_nonzero f s).mpr hn)
  simp only [hz,Finsupp.sum_zero_index]

omit [DecidableEq S] in
lemma unitRows_energy (k : S → ℤ) (f : ∀s,Σn,UnitIndex (a s) n) :
    (unitRowsEquiv a f).val.sum (fun q r=>r • (k q.1-2*(q.2:ℤ)))=
      ∑s,unitEnergy (a s) (f s).1 (k s) (f s).2 := by
  rw [sigma_sum_univ]
  apply Finset.sum_congr rfl
  intro s _
  rw [unitRows_split]
  exact unitRowCount_energy (a s) (f s).1 (k s) (f s).2
end FiniteRows
end
end ElementaryPositivity.UnitSelections
end
end

end OAI
