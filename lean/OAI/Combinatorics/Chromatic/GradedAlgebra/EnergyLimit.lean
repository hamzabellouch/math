import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CountSumDimension
import OAI.Combinatorics.Chromatic.Walls.StringPositiveFactor
import OAI.Combinatorics.Chromatic.Walls.CountEmbedding

namespace OAI

section
namespace ElementaryPositivity.EnergyLaurent
open LaurentPrecision
noncomputable section
variable {A T : Type*} (e : A → ℤ) (he : Admissible e)

include he in
lemma finite_above (L : ℤ) : Set.Finite {a | L≤e a} := by
  obtain ⟨K,hK⟩:=he.1
  let B:=Σ z : Set.Icc L K,{a : A // e a=z.val}
  let (z : Set.Icc L K) : Finite {a : A // e a=z.val} := he.2 z.val
  have hs : Finite {a : A // L≤e a} :=
    Finite.of_injective (fun a : {a : A // L≤e a} =>
      (⟨⟨e a.val,a.property,hK a.val⟩,⟨a.val,rfl⟩⟩ : B)) (by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun x : B=>x.2.val) h)
  exact Set.finite_coe_iff.mp hs

variable (s : A → Finset T)

def finiteSupportCutoff [DecidableEq T] (L : ℤ) : Finset T :=
  (finite_above e he L).toFinset.biUnion s

lemma support_le_cutoff [DecidableEq T] (L : ℤ) (a : A) (ha : L≤e a) :
    s a⊆finiteSupportCutoff e he s L := by
  intro t ht
  exact Finset.mem_biUnion.mpr ⟨a,(finite_above e he L).mem_toFinset.mpr ha,ht⟩

def supportRestrictedSeries (S : Finset T) : LaurentSeries ℚ :=
  series (fun a : {a : A // s a⊆S}=>e a.val)
    (admissible_subtype he (fun a=>s a⊆S))

lemma supportRestricted_coeff (S : Finset T) (j : ℤ)
    (hs : ∀a,e a= -j → s a⊆S) :
    (supportRestrictedSeries e he s S).coeff j=(series e he).coeff j := by
  rw [supportRestrictedSeries,series_coeff,series_coeff]
  congr 1
  apply Nat.card_congr
  exact {
    toFun:=fun a=>⟨a.val.val,a.property⟩
    invFun:=fun a=>⟨⟨a.val,hs a.val a.property⟩,a.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }

lemma supportRestricted_agrees [DecidableEq T] (S : Finset T) (N : ℤ)
    (hs : finiteSupportCutoff e he s (1-N)⊆S) :
    Agrees N (supportRestrictedSeries e he s S) (series e he) := by
  intro j hj
  apply supportRestricted_coeff
  intro a ha
  exact (support_le_cutoff e he s (1-N) a (by omega)).trans hs

theorem finiteSupport_converges :
    Converges (Filter.atTop : Filter (Finset T)) (supportRestrictedSeries e he s) (series e he) := by
  classical
  intro N
  filter_upwards [Filter.eventually_ge_atTop (finiteSupportCutoff e he s (1-N))] with S hS
  exact supportRestricted_agrees e he s S N hS

end
end ElementaryPositivity.EnergyLaurent

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent LaurentPrecision
noncomputable section
attribute [local instance] Classical.propDecidable
variable {S I : Type*} (a : S → ℕ) (dim : S → (I→ℕ)) (k : S → ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))

def startSupport (d : I→ℕ) (f : StringCounts a dim d) : Finset S :=
  f.val.val.support.image Prod.fst

def startEmbedding (T : Finset S) : (T×ℕ) ↪ (S×ℕ) :=
  (Function.Embedding.subtype (fun s=>s∈T)).prodMap (Function.Embedding.refl ℕ)

lemma startSupport_iff (T : Finset S) (d : I→ℕ) (f : StringCounts a dim d) :
    (↑f.val.val.support ⊆ Set.range (startEmbedding T)) ↔ startSupport a dim d f⊆T := by
  classical
  constructor
  · intro H s hs
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hs
    obtain ⟨⟨s,j⟩,he⟩:=H hx
    have HE:=congrArg Prod.fst he
    change s.val=x.1 at HE
    exact HE ▸ s.property
  · intro H x hx
    exact ⟨(⟨x.1,H (Finset.mem_image.mpr ⟨x,hx,rfl⟩)⟩,x.2),rfl⟩

def finiteStartEquiv (T : Finset S) (d : I→ℕ) :
    StringCounts (fun s:T=>a s.val) (fun s:T=>dim s.val) d ≃
      {f : StringCounts a dim d // startSupport a dim d f⊆T} :=
  (dimensionSupportEquiv (startEmbedding T) (fun x:S×ℕ=>a x.1≠0) (fun x=>dim x.1) d).trans
    (Equiv.subtypeEquivRight (startSupport_iff a dim T d))

lemma finiteStart_energy (T : Finset S) (d : I→ℕ)
    (f : StringCounts (fun s:T=>a s.val) (fun s:T=>dim s.val) d) :
    stringEnergy a dim k d (finiteStartEquiv a dim T d f).val=
      stringEnergy (fun s:T=>a s.val) (fun s:T=>dim s.val) (fun s:T=>k s.val) d f :=
  dimensionSupport_energy (startEmbedding T) (fun x:S×ℕ=>a x.1≠0)
    (fun x=>dim x.1) (fun x=>k x.1-2*(x.2:ℤ)) d f

include he in
lemma finiteStart_admissible (T : Finset S) (d : I→ℕ) :
    Admissible (stringEnergy (fun s:T=>a s.val) (fun s:T=>dim s.val) (fun s:T=>k s.val) d) :=
  admissible_injective (admissible_subtype (he d) (fun f=>startSupport a dim d f⊆T))
    (finiteStartEquiv a dim T d) (finiteStartEquiv a dim T d).injective
    (finiteStart_energy a dim k T d)

def finiteStartSeries (T : Finset S) (d : I→ℕ) : LaurentSeries ℚ :=
  stringSeries (fun s:T=>a s.val) (fun s:T=>dim s.val) (fun s:T=>k s.val)
    (finiteStart_admissible a dim k he T) d

lemma finiteStartSeries_eq (T : Finset S) (d : I→ℕ) :
    finiteStartSeries a dim k he T d=
      supportRestrictedSeries (stringEnergy a dim k d) (he d) (startSupport a dim d) T := by
  exact series_equiv _ _ (finiteStartEquiv a dim T d) (finiteStart_energy a dim k T d)

theorem finiteStartSeries_converges (d : I→ℕ) :
    Converges (Filter.atTop : Filter (Finset S)) (fun T=>finiteStartSeries a dim k he T d)
      (stringSeries a dim k he d) := by
  simp_rw [finiteStartSeries_eq]
  exact finiteSupport_converges (stringEnergy a dim k d) (he d) (startSupport a dim d)
end
end ElementaryPositivity.UnitSelections

end
section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity EnergyLaurent
noncomputable section
variable {S T I : Type*} (a : S→ℕ) (dim : S→(I→ℕ)) (k : S→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))

lemma stringSeries_congr (b : S→ℕ) (dim' : S→(I→ℕ)) (k' : S→ℤ)
    (he' : ∀d,Admissible (stringEnergy b dim' k' d))
    (ha : a=b) (hd : dim=dim') (hk : k=k') :
    stringSeries a dim k he=stringSeries b dim' k' he' := by
  cases ha
  cases hd
  cases hk
  rfl

lemma stringSeries_reindex (e : T ≃ S) (d : I→ℕ) :
    stringSeries (fun s=>a (e s)) (fun s=>dim (e s)) (fun s=>k (e s))
      (stringReindex_admissible e a dim k he) d=stringSeries a dim k he d :=
  series_equiv _ _ (stringReindex e a dim d) (stringReindex_energy e a dim k d)

include he in
lemma stringEmbedding_admissible (e : T ↪ S) (d : I→ℕ) :
    Admissible (stringEnergy (fun s=>a (e s)) (fun s=>dim (e s)) (fun s=>k (e s)) d) := by
  let E:=e.prodMap (Function.Embedding.refl ℕ)
  let F:=dimensionSupportEquiv E (fun x:S×ℕ=>a x.1≠0) (fun x=>dim x.1) d
  exact admissible_injective (he d) (fun f=>(F f).val)
    (fun x y h=>F.injective (Subtype.ext h))
    (dimensionSupport_energy E (fun x:S×ℕ=>a x.1≠0) (fun x=>dim x.1)
      (fun x=>k x.1-2*(x.2:ℤ)) d)

lemma stringSeries_zero (hdim : ∀s,dim s≠0) : stringSeries a dim k he 0=1 := by
  have hE : ∀f : StringCounts a dim 0,stringEnergy a dim k 0 f=0 :=
    fun f=>dimensionCounts_zero_energy (fun x:S×ℕ=>a x.1≠0) (fun x=>dim x.1)
      (fun x=>hdim x.1) (fun x=>k x.1-2*(x.2:ℤ)) f
  let := dimensionCounts_zero_subsingleton (fun x:S×ℕ=>a x.1≠0) (fun x=>dim x.1) (fun x=>hdim x.1)
  let : Nonempty (StringCounts a dim 0) := ⟨⟨zeroCount _,countDimension_zero _ _⟩⟩
  ext j
  rw [stringSeries,series_coeff,HahnSeries.coeff_one]
  by_cases hj : j=0
  · subst j
    have H : ∀f : StringCounts a dim 0,stringEnergy a dim k 0 f= -0 := by simpa using hE
    simp only [H,neg_zero]
    simp
  · let : IsEmpty {f : StringCounts a dim 0 // stringEnergy a dim k 0 f= -j} :=
      ⟨fun f=>hj (by have HH:=f.property; rw [hE] at HH; omega)⟩
    simp [hj]

lemma stringSeries_empty [IsEmpty S] (d : I→ℕ) (hd : d≠0) : stringSeries a dim k he d=0 := by
  let : IsEmpty (StringCounts a dim d) := ⟨fun f=>by
    apply hd
    rw [←f.property,countDimension]
    exact Finset.sum_eq_zero (fun x _=>isEmptyElim x.1)⟩
  ext j
  rw [stringSeries,series_coeff]
  simp
end
end ElementaryPositivity.UnitSelections

end

end OAI
