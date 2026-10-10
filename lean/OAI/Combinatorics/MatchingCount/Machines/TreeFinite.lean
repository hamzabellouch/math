import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPCounts
import OAI.Combinatorics.MatchingCount.Machines.TreeCanonical

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

def Realizer.recode {f : C → D} (F : Realizer f) (i : A → C) (g : A → B)
    (hi : ∀ a,encode (i a)=encode a) (ho : ∀ a,encode (f (i a))=encode (g a)) : Realizer g where
  program := F.program
  cost := fun a=>F.cost (i a)
  correct := by
    intro a s
    have h:=F.correct (i a) s
    rw [hi,ho] at h
    exact h
lemma polynomial_recode {f : C → D} {F : Realizer f} (i : A → C) (g : A → B)
    (hi : ∀ a,encode (i a)=encode a) (ho : ∀ a,encode (f (i a))=encode (g a))
    (hF : PolynomialTime F) : PolynomialTime (F.recode i g hi ho) := by
  obtain ⟨p,hp⟩:=hF
  refine ⟨p,fun a=>?_⟩
  have h:=hp (i a)
  change F.cost (i a)+weight (g a)≤_
  simpa only [weight,hi,ho] using h

instance finsetCodec [LinearOrder A] : Codec (Finset A) := ⟨fun s=>encode (s.sort (·≤·))⟩
@[simp] lemma encode_finset [LinearOrder A] (s : Finset A) : encode s=encode (s.sort (·≤·)) := rfl
@[simp] lemma weight_finset [LinearOrder A] (s : Finset A) : weight s=weight (s.sort (·≤·)) := rfl
variable [LinearOrder A]

def finsetList : Realizer (fun s : Finset A=>s.sort (·≤·)) :=
  (identity (A:=List A)).recode (fun s : Finset A=>s.sort (·≤·)) (fun s=>s.sort (·≤·)) (fun _=>rfl) (fun _=>rfl)
lemma polynomial_finsetList : PolynomialTime (finsetList (A:=A)) := by
  unfold finsetList
  exact polynomial_recode _ _ _ _ polynomial_identity

def listFinset (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (List.toFinset (α:=A)) :=
  (canonical (·≤·) E R).recode id List.toFinset (fun _=>rfl) (fun as=>by
    change encode (as.dedup.insertionSort (·≤·))=encode (as.toFinset.sort (·≤·))
    rw [canonical_eq_sort])
lemma polynomial_listFinset {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (listFinset E R) := by
  unfold listFinset
  exact polynomial_recode _ _ _ _ (polynomial_canonical _ hE hR)

def finsetMember (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : A×Finset A=>decide (x.1∈x.2)) :=
  (contains E).recode (fun x=>(x.1,x.2.sort (·≤·))) _ (fun _=>rfl) (fun x=>by simp)
lemma polynomial_finsetMember {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetMember E) := by
  unfold finsetMember
  exact polynomial_recode _ _ _ _ (polynomial_contains hE)

def finsetCard : Realizer (Finset.card (α:=A)) :=
  (composition finsetList listLength).congr (by intro s; simp)
lemma polynomial_finsetCard : PolynomialTime (finsetCard (A:=A)) := by
  unfold finsetCard
  exact polynomial_congr _ (polynomial_composition polynomial_finsetList polynomial_listLength)

def finsetUnion (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) :
    Realizer (fun x : Finset A×Finset A=>x.1∪x.2) :=
  (composition (composition (pair (composition first finsetList) (composition second finsetList)) append)
    (listFinset E R)).congr (by intro x; simp)
lemma polynomial_finsetUnion {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (finsetUnion E R) := by
  unfold finsetUnion
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_finsetList)
      (polynomial_composition polynomial_second polynomial_finsetList)) polynomial_append)
    (polynomial_listFinset hE hR))

def finsetImage [LinearOrder B] {f : A → B} (F : Realizer f)
    (E : Realizer (fun x : B×B=>decide (x.1=x.2)))
    (R : Realizer (fun x : B×B=>decide (x.1≤x.2))) :
    Realizer (Finset.image f) :=
  (composition (composition finsetList (map F)) (listFinset E R)).congr (by intro s; ext a; simp)
lemma polynomial_finsetImage [LinearOrder B] {f : A → B} {F : Realizer f}
    {E : Realizer (fun x : B×B=>decide (x.1=x.2))}
    {R : Realizer (fun x : B×B=>decide (x.1≤x.2))}
    (hF : PolynomialTime F) (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (finsetImage F E R) := by
  unfold finsetImage
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition polynomial_finsetList (polynomial_map hF)) (polynomial_listFinset hE hR))

omit [Codec A] in
lemma sort_filter (p : A → Bool) (s : Finset A) :
    (s.sort (·≤·)).filter p=(s.filter fun a=>p a).sort (·≤·) := by
  have hh := (List.toFinset_sort (r:=(·≤·)) ((Finset.sort_nodup s (·≤·)).filter p)).mpr
    ((Finset.pairwise_sort s (·≤·)).filter p)
  simpa only [List.toFinset_filter,Finset.sort_toFinset] using hh.symm

def finsetFilter {p : A → Bool} (P : Realizer p) : Realizer (fun s : Finset A=>s.filter fun a=>p a) :=
  (filter P).recode (fun s=>s.sort (·≤·)) _ (fun _=>rfl) (fun s=>by
    change encode ((s.sort (·≤·)).filter p)=encode ((s.filter fun a=>p a).sort (·≤·))
    rw [sort_filter])
lemma polynomial_finsetFilter {p : A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (finsetFilter P) := by
  unfold finsetFilter
  exact polynomial_recode _ _ _ _ (polynomial_filter hP)

def finsetFilterWith {p : B×A → Bool} (P : Realizer p) :
    Realizer (fun x : B×Finset A=>x.2.filter fun a=>p (x.1,a)) :=
  (filterWith P).recode (fun x=>(x.1,x.2.sort (·≤·))) _ (fun _=>rfl) (fun x=>by
    change encode ((x.2.sort (·≤·)).filter fun a=>p (x.1,a))=encode ((x.2.filter fun a=>p (x.1,a)).sort (·≤·))
    rw [sort_filter])

omit [LinearOrder A] in
lemma polynomial_filterWith {p : B×A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (filterWith P) := by
  unfold filterWith
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_mapWith (polynomial_pair polynomial_second hP))
      (polynomial_filter polynomial_second)) (polynomial_map polynomial_first))
lemma polynomial_finsetFilterWith {p : B×A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (finsetFilterWith P) := by
  unfold finsetFilterWith
  exact polynomial_recode _ _ _ _ (polynomial_filterWith hP)

end MatchingFPRAS.TreeTyped

end OAI
