import Mathlib
import OAI.Probability.SKGap.Localization.BlockDegree
import OAI.Probability.SKGap.Localization.NoiseSplit

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace Diagram
variable {D E : Type*}

def NoiseSplit.map (f : D→E) {F : List (Letter D)} (s : NoiseSplit F) :
    NoiseSplit (F.map (Letter.map f)) where
  before := s.before.map (Letter.map f)
  after := s.after.map (Letter.map f)
  word_eq := by simpa [Letter.map] using congrArg (List.map (Letter.map f)) s.word_eq

lemma NoiseSplit.map_bijective (f : D→E) (F : List (Letter D)) :
    Function.Bijective (NoiseSplit.map f (F := F)) := by
  constructor
  · intro s t h
    apply NoiseSplit.code_injective F
    apply Fin.ext
    have hh := congrArg (fun s => s.before.length) h
    simpa [NoiseSplit.map,NoiseSplit.code] using hh
  · intro s
    obtain ⟨p,q,hF,hp,hq⟩ := List.map_eq_append_iff.mp s.word_eq
    cases q with
    | nil => simp at hq
    | cons l q =>
      cases l with
      | diag a => simp [Letter.map] at hq
      | noise =>
        simp only [List.map_cons,Letter.map,List.cons.injEq,true_and] at hq
        refine ⟨⟨p,q,hF⟩,?_⟩
        apply NoiseSplit.ext <;> simp [NoiseSplit.map,hp,hq]

def NoiseSplit.mapEquiv (f : D→E) (F : List (Letter D)) :
    NoiseSplit F ≃ NoiseSplit (F.map (Letter.map f)) :=
  Equiv.ofBijective (NoiseSplit.map f) (NoiseSplit.map_bijective f F)

def NoiseSplit.appendLeft (P Q : List (Letter D)) (s : NoiseSplit P) :
    NoiseSplit (P++Q) :=
  ⟨s.before,s.after++Q,by
    simpa only [List.append_assoc,List.cons_append] using
      congrArg (fun f => f++Q) s.word_eq⟩
def NoiseSplit.appendRight (P Q : List (Letter D)) (s : NoiseSplit Q) :
    NoiseSplit (P++Q) :=
  ⟨P++s.before,s.after,by
    simpa only [List.append_assoc] using
      congrArg (fun f => P++f) s.word_eq⟩

def NoiseSplit.appendMap (P Q : List (Letter D)) :
    NoiseSplit P ⊕ NoiseSplit Q → NoiseSplit (P++Q) :=
  Sum.elim (NoiseSplit.appendLeft P Q) (NoiseSplit.appendRight P Q)

lemma take_noise_drop {F : List (Letter D)} {k : ℕ} (h : F[k]?=some .noise) :
    F=F.take k++(.noise::F.drop (k+1)) := by
  have he := List.take_append_drop k F
  rw [List.drop_eq_getElem?_toList_append,h] at he
  simpa using he.symm

lemma NoiseSplit.appendMap_bijective (P Q : List (Letter D)) :
    Function.Bijective (NoiseSplit.appendMap P Q) := by
  constructor
  · intro s t h
    cases s with
    | inl s =>
      cases t with
      | inl t =>
        apply congrArg Sum.inl
        apply NoiseSplit.code_injective P
        apply Fin.ext
        exact congrArg (fun s => s.before.length) h
      | inr t =>
        have hh := congrArg (fun s => s.before.length) h
        change s.before.length=(P++t.before).length at hh
        have hs := s.length_bound
        simp only [List.length_append] at hh
        omega
    | inr s =>
      cases t with
      | inl t =>
        have hh := congrArg (fun s => s.before.length) h
        change (P++s.before).length=t.before.length at hh
        have ht := t.length_bound
        simp only [List.length_append] at hh
        omega
      | inr t =>
        apply congrArg Sum.inr
        apply NoiseSplit.code_injective Q
        apply Fin.ext
        have hh := congrArg (fun s => s.before.length) h
        change (P++s.before).length=(P++t.before).length at hh
        simpa [NoiseSplit.code] using hh
  · intro s
    by_cases h : s.before.length<P.length
    · have he : (P++Q)[s.before.length]?=some .noise := by
        simpa using congrArg (fun f => f[s.before.length]?) s.word_eq
      have hP : P[s.before.length]?=some .noise := by simpa [List.getElem?_append,h] using he
      let t : NoiseSplit P :=
        ⟨P.take s.before.length,P.drop (s.before.length+1),
          take_noise_drop hP⟩
      refine ⟨.inl t,?_⟩
      apply NoiseSplit.code_injective (P++Q)
      apply Fin.ext
      change (P.take s.before.length).length=s.before.length
      simp [Nat.min_eq_left h.le]
    · have he : (P++Q)[s.before.length]?=some .noise := by
        simpa using congrArg (fun f => f[s.before.length]?) s.word_eq
      have hQ : Q[s.before.length-P.length]?=some .noise := by
        simpa [List.getElem?_append,h] using he
      let t : NoiseSplit Q :=
        ⟨Q.take (s.before.length-P.length),Q.drop (s.before.length-P.length+1),
          take_noise_drop hQ⟩
      refine ⟨.inr t,?_⟩
      apply NoiseSplit.code_injective (P++Q)
      apply Fin.ext
      change (P++Q.take (s.before.length-P.length)).length=s.before.length
      have hs := s.length_bound
      simp only [List.length_append,List.length_take]
      simp only [List.length_append] at hs
      rw [Nat.min_eq_left (by omega)]
      omega

def NoiseSplit.appendEquiv (P Q : List (Letter D)) :
    (NoiseSplit P ⊕ NoiseSplit Q) ≃ NoiseSplit (P++Q) :=
  Equiv.ofBijective (NoiseSplit.appendMap P Q) (NoiseSplit.appendMap_bijective P Q)

lemma NoiseSplit.sum_append {M : Type*} [AddCommMonoid M]
    (P Q : List (Letter D)) (f : List (Letter D)→List (Letter D)→M) :
    (∑ s : NoiseSplit (P++Q), f s.before s.after) =
      (∑ s : NoiseSplit P, f s.before (s.after++Q))+
      (∑ s : NoiseSplit Q, f (P++s.before) s.after) := by
  have he := Fintype.sum_equiv (NoiseSplit.appendEquiv P Q)
    (fun s => match s with
      | .inl s => f s.before (s.after++Q)
      | .inr s => f (P++s.before) s.after)
    (fun s => f s.before s.after) (by intro s; cases s <;> rfl)
  rw [← he,Fintype.sum_sum_type]

end Diagram
end SKGap.Noncrossing

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace InverseDiagram
open Diagram

lemma expandBlocks_injective : Function.Injective expandBlocks := by
  intro p q h
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => rfl
    | cons b q => cases b <;> simp at h
  | cons b p ih =>
    cases q with
    | nil => cases b <;> simp at h
    | cons c q =>
      cases b <;> cases c <;> simp only [expandBlocks_false,
        expandBlocks_true,List.cons.injEq,Letter.diag.injEq,Bool.false_eq_true,
        Bool.true_eq_false,false_and,true_and] at h
      · exact congrArg (false::·) (ih h)
      · exact congrArg (true::·) (ih h)

@[simp] lemma blockDegree_append (p q : List Bool) :
    blockDegree (p++q)=blockDegree p+blockDegree q := by simp [blockDegree]

def SplitBlocks (n : ℕ) := {pq : List Bool × List Bool // blockDegree pq.1+blockDegree pq.2=n}
def SplitChoices (n : ℕ) := Σ k : Fin (n+1), Blocks k.val × Blocks (n-k.val)
def MarkedBlocks (n : ℕ) := Σ bs : Blocks (n+1), NoiseSplit (expandBlocks bs.val)

instance splitChoicesFintype (n : ℕ) : Fintype (SplitChoices n) := inferInstanceAs
  (Fintype (Σ k : Fin (n+1), Blocks k.val × Blocks (n-k.val)))
instance markedBlocksFintype (n : ℕ) : Fintype (MarkedBlocks n) := inferInstanceAs
  (Fintype (Σ bs : Blocks (n+1), NoiseSplit (expandBlocks bs.val)))

def splitChoice (n : ℕ) (z : SplitChoices n) : SplitBlocks n :=
  ⟨(z.2.1.val,z.2.2.val),by
    rw [z.2.1.property,z.2.2.property]
    have h := z.1.isLt
    omega⟩

lemma splitChoice_bijective (n : ℕ) : Function.Bijective (splitChoice n) := by
  constructor
  · rintro ⟨k,p,q⟩ ⟨l,r,s⟩ h
    have hp : p.val=r.val := congrArg (fun z => z.val.1) h
    have hq : q.val=s.val := congrArg (fun z => z.val.2) h
    have hk : k=l := by
      apply Fin.ext
      simpa only [p.property,r.property] using congrArg blockDegree hp
    subst l
    have hp' : p=r := Subtype.ext hp
    have hq' : q=s := Subtype.ext hq
    subst r; subst s; rfl
  · intro p
    refine ⟨⟨⟨blockDegree p.val.1,by have h := p.property; omega⟩,
      ⟨p.val.1,rfl⟩,⟨p.val.2,by
        change blockDegree p.val.2=n-blockDegree p.val.1
        have h := p.property; omega⟩⟩,?_⟩
    rfl

def splitChoiceEquiv (n : ℕ) : SplitChoices n ≃ SplitBlocks n :=
  Equiv.ofBijective (splitChoice n) (splitChoice_bijective n)
instance splitBlocksFintype (n : ℕ) : Fintype (SplitBlocks n) :=
  Fintype.ofEquiv (SplitChoices n) (splitChoiceEquiv n)

def splitToMarked (n : ℕ) (p : SplitBlocks n) : MarkedBlocks n :=
  ⟨⟨p.val.1++(true::p.val.2),by
      simp only [blockDegree_append,blockDegree_true]
      have h := p.property; omega⟩,
    ⟨expandBlocks p.val.1++[.diag true],expandBlocks p.val.2,by
      simp only [expandBlocks_append,expandBlocks_true,List.append_assoc,List.cons_append,
        List.nil_append]⟩⟩

lemma splitToMarked_bijective (n : ℕ) : Function.Bijective (splitToMarked n) := by
  constructor
  · intro p q h
    apply Subtype.ext
    apply Prod.ext
    · apply expandBlocks_injective
      have he := congrArg (fun z : MarkedBlocks n => z.2.before) h
      change expandBlocks p.val.1++[.diag true]=expandBlocks q.val.1++[.diag true] at he
      exact List.append_cancel_right he
    · apply expandBlocks_injective
      exact congrArg (fun z : MarkedBlocks n => z.2.after) h
  · rintro ⟨⟨bs,hbs⟩,s⟩
    obtain ⟨p,q,hpq,hp,hq⟩ := split_noise bs s.before s.after s.word_eq
    have hd : blockDegree p+blockDegree q=n := by
      rw [hpq,blockDegree_append,blockDegree_true] at hbs
      omega
    refine ⟨⟨(p,q),hd⟩,?_⟩
    subst bs
    have hs : (splitToMarked n ⟨(p,q),hd⟩).snd = s := by
      apply NoiseSplit.ext
      · exact hp.symm
      · exact hq.symm
    exact congrArg (Sigma.mk (⟨p++true::q,hbs⟩ : Blocks (n+1))) hs

def markedBlockEquiv (n : ℕ) : SplitChoices n ≃ MarkedBlocks n :=
  (splitChoiceEquiv n).trans (Equiv.ofBijective (splitToMarked n) (splitToMarked_bijective n))

theorem sum_marked_blocks {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : List (Letter Bool)→List (Letter Bool)→M) :
    (∑ bs : Blocks (n+1), ∑ s : NoiseSplit (expandBlocks bs.val), f s.before s.after) =
      ∑ k : Fin (n+1), ∑ p : Blocks k.val, ∑ q : Blocks (n-k.val),
        f (expandBlocks p.val++[.diag true]) (expandBlocks q.val) := by
  have he := Fintype.sum_equiv (markedBlockEquiv n)
    (fun z => f (expandBlocks z.2.1.val++[.diag true]) (expandBlocks z.2.2.val))
    (fun z => f z.2.before z.2.after) (by intro z; rfl)
  change (∑ z : Σ k : Fin (n+1), Blocks k.val × Blocks (n-k.val),
    f (expandBlocks z.2.1.val++[.diag true]) (expandBlocks z.2.2.val)) =
    (∑ z : Σ bs : Blocks (n+1), NoiseSplit (expandBlocks bs.val),
      f z.2.before z.2.after) at he
  rw [Fintype.sum_sigma,Fintype.sum_sigma] at he
  simp_rw [Fintype.sum_prod_type] at he
  exact he.symm

end InverseDiagram
end SKGap.Noncrossing

noncomputable section
open scoped BigOperators

end
end
end
end
end
end
end
end
end
end

end OAI
