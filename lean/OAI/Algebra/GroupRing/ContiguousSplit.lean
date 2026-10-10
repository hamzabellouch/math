import Mathlib
import OAI.Algebra.GroupRing.ClosedWords

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ContiguousSplit
open scoped Classical
open PermutationCycles
lemma rotate_val {n : ℕ} (i : Fin n) :
    (finRotate n i).val=if i.val+1=n then 0 else i.val+1 := by
  cases n with
  | zero=>exact i.elim0
  | succ n=>
    rw [coe_finRotate]
    have hh : i=Fin.last n ↔ i.val+1=n+1 := by
      constructor
      · rintro rfl;rfl
      · intro successor_eq
        exact Fin.ext (Nat.add_right_cancel successor_eq)
    simp only [hh]
variable (n m : ℕ)
abbrev O := Fin (n+1)⊕Fin (m+1)
def split : Equiv.Perm (O n m) := Equiv.sumCongr (finRotate (n+1)) (finRotate (m+1))
def joined : Equiv.Perm (O n m) := Equiv.swap (.inl 0) (.inr 0)*split n m
lemma joined_commutes (x : O n m) :
    finSumFinEquiv (joined n m x)=finRotate ((n+1)+(m+1)) (finSumFinEquiv x) := by
  cases x with
  | inl i=>
    by_cases hi : i=Fin.last n
    · subst i
      simp only [joined,split,Equiv.Perm.mul_apply,Equiv.sumCongr_apply,Sum.map_inl,
        finRotate_last,Equiv.swap_apply_left,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right]
      apply Fin.ext
      rw [rotate_val]
      simp only [Fin.val_natAdd,Fin.val_zero,add_zero,Fin.val_castAdd,Fin.val_last]
      rw [ite_eq_right (by omega)]
    · have hn : finRotate (n+1) i≠0 := by
        intro hh
        have h : finRotate (n+1) i=finRotate (n+1) (Fin.last n) := hh.trans (finRotate_last (n:=n)).symm
        exact hi ((finRotate _).injective h)
      simp only [joined,split,Equiv.Perm.mul_apply,Equiv.sumCongr_apply,Sum.map_inl]
      rw [Equiv.swap_apply_of_ne_of_ne (by simpa using hn) (by simp)]
      simp only [finSumFinEquiv_apply_left]
      apply Fin.ext
      rw [Fin.val_castAdd,rotate_val,rotate_val]
      have hit : i.val < n := (Fin.lt_last_iff_ne_last).mpr hi
      simp only [Fin.val_castAdd]
      rw [ite_eq_right (by omega),ite_eq_right (by omega)]
  | inr i=>
    by_cases hi : i=Fin.last m
    · subst i
      simp only [joined,split,Equiv.Perm.mul_apply,Equiv.sumCongr_apply,Sum.map_inr,
        finRotate_last,Equiv.swap_apply_right,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right]
      apply Fin.ext
      rw [rotate_val]
      simp only [Fin.val_castAdd,Fin.val_zero,Fin.val_natAdd,Fin.val_last]
      rw [ite_eq_left (by omega)]
    · have hn : finRotate (m+1) i≠0 := by
        intro hh
        have h : finRotate (m+1) i=finRotate (m+1) (Fin.last m) := hh.trans (finRotate_last (n:=m)).symm
        exact hi ((finRotate _).injective h)
      simp only [joined,split,Equiv.Perm.mul_apply,Equiv.sumCongr_apply,Sum.map_inr]
      rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hn)]
      simp only [finSumFinEquiv_apply_right]
      apply Fin.ext
      rw [Fin.val_natAdd,rotate_val,rotate_val]
      have hit : i.val < m := (Fin.lt_last_iff_ne_last).mpr hi
      simp only [Fin.val_natAdd]
      rw [ite_eq_right (by omega),ite_eq_right (by omega)]
      omega
lemma joined_conjugate : joined n m=finSumFinEquiv.symm.permCongr (finRotate ((n+1)+(m+1))) := by
  apply Equiv.ext
  intro x
  apply finSumFinEquiv.injective
  simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply,joined_commutes]
lemma joined_sameCycle (x y : O n m) : (joined n m).SameCycle x y := by
  rw [joined_conjugate]
  have hh := WordPairing.rotate_sameCycle (show 2≤(n+1)+(m+1) by omega)
    (finSumFinEquiv x) (finSumFinEquiv y)
  have ht := PermutationTransport.sameCycle finSumFinEquiv.symm (finRotate ((n+1)+(m+1))) hh
  simpa only [Equiv.symm_apply_apply] using ht
/-- A literal contiguous cut of one cyclic boundary preserves genus zero for
any actual involutive matching, including bands across the cut. -/
theorem genusZero (α : Equiv.Perm (O n m)) (hi : Function.Involutive α)
    (hz : MapEuler.GenusZero (joined n m) α) : MapEuler.GenusZero (split n m) α := by
  have hh := MapEuler.genusZero_vertexSplit (joined n m) α hi hz
    (.inl 0) (.inr 0) (by simp) ((cycle_eq _).mpr (joined_sameCycle n m _ _))
  have he : Equiv.swap (Sum.inl (0 : Fin (n+1))) (Sum.inr (0 : Fin (m+1))) *
      joined n m=split n m := by
    ext x
    simp only [joined,Equiv.Perm.mul_apply]
    convert Equiv.swap_apply_self (Sum.inl (0 : Fin (n+1)))
      (Sum.inr (0 : Fin (m+1))) (split n m x) using 1
  have hh' : MapEuler.GenusZero (Equiv.swap (Sum.inl (0 : Fin (n+1)))
      (Sum.inr (0 : Fin (m+1))) * joined n m) α := by
    convert hh using 1
    apply Equiv.ext
    intro x
    simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_def]
    split_ifs <;> rfl
  rw [he] at hh'
  exact hh' 

end TorsionFreeZeroDivisors.ContiguousSplit
namespace TorsionFreeZeroDivisors.BoundaryRefinement
open scoped Classical
open PermutationCycles
variable {O : Type}
/-- Finite sequences of actual vertex cuts. This retains the whole matching;
only cyclic boundary order changes. Cuts must occur on the same current cycle. -/
inductive Cuts : Equiv.Perm O → Equiv.Perm O → Prop
  | refl (σ) : Cuts σ σ
  | step (σ) (p q : O) (hne : p≠q) (hcycle : σ.SameCycle p q) :
      Cuts σ (Equiv.swap p q*σ)
  | trans {σ τ υ} : Cuts σ τ → Cuts τ υ → Cuts σ υ
variable [Fintype O]
lemma preserves {σ τ : Equiv.Perm O} (h : Cuts σ τ) (α : Equiv.Perm O)
    (hi : Function.Involutive α) (hz : MapEuler.GenusZero σ α) :
    MapEuler.GenusZero τ α := by
  induction h with
  | refl=>exact hz
  | step σ p q hn hc=>
    have hh := MapEuler.genusZero_vertexSplit σ α hi hz p q hn ((cycle_eq σ).mpr hc)
    convert hh using 1
  | trans h h' ih ih'=>exact ih' (ih hz)
lemma mapped_sameCycle {P : Type} (f : O→P) (σ : Equiv.Perm O) (τ : Equiv.Perm P)
    (hc : ∀x,τ (f x)=f (σ x)) {x y : O} (h : σ.SameCycle x y) :
    τ.SameCycle (f x) (f y) := by
  obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
  have he : ∀k x,(τ^k) (f x)=f ((σ^k) x) := by
    intro k
    induction k with
    | zero=>intro x;rfl
    | succ k ih=>intro x;simp only [pow_succ',Equiv.Perm.mul_apply,ih,hc]
  exact ⟨(k:ℤ),by rw [zpow_natCast,he,hk]⟩
variable {P : Type} [Fintype P]
omit [Fintype P] in
lemma conjugate {σ τ : Equiv.Perm O} (h : Cuts σ τ) (e : O≃P) :
    Cuts (e.permCongr σ) (e.permCongr τ) := by
  induction h with
  | refl=>exact .refl _
  | step σ p q hn hc=>
    have hex : e.permCongr (Equiv.swap p q*σ)=Equiv.swap (e p) (e q)*e.permCongr σ := by
      apply Equiv.ext
      intro x
      simp only [Equiv.permCongr_apply,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
      have he₂ : σ (e.symm x)=p ↔ e (σ (e.symm x))=e p := e.injective.eq_iff.symm
      have he₃ : σ (e.symm x)=q ↔ e (σ (e.symm x))=e q := e.injective.eq_iff.symm
      split_ifs <;> first | rfl | simp_all
    rw [hex]
    exact .step _ _ _ (fun h=>hn (e.injective h)) (PermutationTransport.sameCycle e σ hc)
  | trans h h' ih ih'=>exact ih.trans ih'
omit [Fintype P] in
lemma left {σ τ : Equiv.Perm O} (h : Cuts σ τ) (ρ : Equiv.Perm P) :
    Cuts (Equiv.sumCongr σ ρ) (Equiv.sumCongr τ ρ) := by
  let : DecidableEq (O⊕P) := fun _ _=>Classical.propDecidable _
  induction h with
  | refl=>exact .refl _
  | step σ p q hn hc=>
    have hex : Equiv.sumCongr (Equiv.swap p q*σ) ρ=
        Equiv.swap (Sum.inl p) (Sum.inl q)*Equiv.sumCongr σ ρ := by
      apply Equiv.ext
      intro x
      cases x with
      | inl x=>simp [Equiv.Perm.mul_apply,Equiv.swap_apply_def];split_ifs <;> simp_all
      | inr x=>simp [Equiv.Perm.mul_apply,Equiv.swap_apply_def]
    rw [hex]
    exact .step _ _ _ (fun h=>hn (Sum.inl.inj h))
      (mapped_sameCycle Sum.inl σ (Equiv.sumCongr σ ρ) (fun _=>rfl) hc)
  | trans h h' ih ih'=>exact ih.trans ih'
lemma right {σ τ : Equiv.Perm P} (h : Cuts σ τ) (ρ : Equiv.Perm O) :
    Cuts (Equiv.sumCongr ρ σ) (Equiv.sumCongr ρ τ) := by
  have hh := conjugate (left h ρ) (Equiv.sumComm P O)
  convert hh using 1 <;> apply Equiv.ext <;> intro x <;> cases x <;> rfl

end TorsionFreeZeroDivisors.BoundaryRefinement
namespace TorsionFreeZeroDivisors.BlockBoundary
open scoped Classical
open BoundaryRefinement
lemma fin_cut (n m : ℕ) : Cuts
    (finSumFinEquiv.symm.permCongr (finRotate (n+m)))
    (Equiv.sumCongr (finRotate n) (finRotate m)) := by
  cases n with
  | zero=>
    have he : finSumFinEquiv.symm.permCongr (finRotate (0+m))=
        Equiv.sumCongr (finRotate 0) (finRotate m) := by
      apply Equiv.ext
      intro x
      cases x with
      | inl x=>exact x.elim0
      | inr x=>
        apply finSumFinEquiv.injective
        simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply,
          Equiv.sumCongr_apply,Sum.map_inr,finSumFinEquiv_apply_right]
        simp
        apply Fin.ext
        simp [Fin.val_add]
    rw [he];exact .refl _
  | succ n=>
    cases m with
    | zero=>
      have he : finSumFinEquiv.symm.permCongr (finRotate ((n+1)+0))=
          Equiv.sumCongr (finRotate (n+1)) (finRotate 0) := by
        apply Equiv.ext
        intro x
        cases x with
        | inr x=>exact x.elim0
        | inl x=>
          apply finSumFinEquiv.injective
          simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply,
            Equiv.sumCongr_apply,Sum.map_inl,finSumFinEquiv_apply_left]
          congr 1
      rw [he];exact .refl _
    | succ m=>
      rw [←ContiguousSplit.joined_conjugate n m]
      have hh := Cuts.step (ContiguousSplit.joined n m)
        (Sum.inl (0 : Fin (n+1))) (Sum.inr (0 : Fin (m+1)))
        (by simp) (ContiguousSplit.joined_sameCycle n m _ _)
      have he : Equiv.swap (Sum.inl (0 : Fin (n+1))) (Sum.inr (0 : Fin (m+1))) *
          ContiguousSplit.joined n m=ContiguousSplit.split n m := by
        apply Equiv.ext
        intro x
        simp only [ContiguousSplit.joined,Equiv.Perm.mul_apply]
        convert Equiv.swap_apply_self (Sum.inl (0 : Fin (n+1)))
          (Sum.inr (0 : Fin (m+1))) (ContiguousSplit.split n m x) using 1
      have hh' : Cuts (ContiguousSplit.joined n m)
          (Equiv.swap (Sum.inl (0 : Fin (n+1))) (Sum.inr (0 : Fin (m+1))) *
          ContiguousSplit.joined n m) := by
        convert hh using 1
        apply Equiv.ext
        intro x
        simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_def]
        split_ifs <;> rfl
      rw [he] at hh'
      exact hh'
/-- Each original block has its own actual finite cyclic boundary. Empty
blocks contribute no occurrences, rather than an artificial marked vertex. -/
def Occ : List ℕ→Type
  | []=>Empty
  | n::ns=>Fin n⊕Occ ns
instance (ns : List ℕ) : Fintype (Occ ns) := by
  induction ns with
  | nil=>exact inferInstanceAs (Fintype Empty)
  | cons n ns ih=>
    let : Fintype (Occ ns) := ih
    exact inferInstanceAs (Fintype (Fin n⊕Occ ns))

def coordinates : (ns : List ℕ)→Occ ns≃Fin ns.sum
  | []=>@Equiv.equivOfIsEmpty Empty (Fin 0) inferInstance inferInstance
  | _n::ns=>(Equiv.sumCongr (Equiv.refl _) (coordinates ns)).trans finSumFinEquiv

def rotation : (ns : List ℕ)→Equiv.Perm (Occ ns)
  | []=>1
  | n::ns=>Equiv.sumCongr (finRotate n) (rotation ns)
def full (ns : List ℕ) : Equiv.Perm (Occ ns) :=
  (coordinates ns).symm.permCongr (finRotate ns.sum)
/-- Split the flattened boundary at every literal word boundary. The
matching is retained in full, including pairs joining different blocks. -/
theorem refinement (ns : List ℕ) : Cuts (full ns) (rotation ns) := by
  induction ns with
  | nil=>
    have he : full []=rotation [] := by
      apply Equiv.ext
      intro x
      exact Empty.elim x
    rw [he];exact .refl _
  | cons n ns ih=>
    let e : Fin n⊕Fin ns.sum≃Occ (n::ns) :=
      Equiv.sumCongr (Equiv.refl _) (coordinates ns).symm
    have hh := conjugate (fin_cut n ns.sum) e
    have he₁ : e.permCongr (finSumFinEquiv.symm.permCongr (finRotate (n+ns.sum)))=
        full (n::ns) := by
      rfl
    have he₂ : e.permCongr (Equiv.sumCongr (finRotate n) (finRotate ns.sum))=
        Equiv.sumCongr (finRotate n) (full ns) := by
      apply Equiv.ext
      intro x
      cases x <;> rfl
    rw [he₁,he₂] at hh
    exact hh.trans (right ih (finRotate n))
variable {A : Type*} {ns : List ℕ} {inv : A→A} {label : Fin ns.sum→A}
/-- Any actual disk word matching induces a genus-zero matching on all its
literal blocks. This alone does not remove conjugator occurrences. -/
theorem genusZero (d : WordPairing.Data inv label) :
    MapEuler.GenusZero (rotation ns) ((coordinates ns).symm.permCongr d.partner) :=
  preserves (refinement ns) _ (PermutationTransport.involutive _ _ d.involutive)
    (MapConjugation.genusZero (coordinates ns).symm _ _ d.genusZero)

end TorsionFreeZeroDivisors.BlockBoundary
/-! Algebraic disk-picture certificates. The relator words are retained literally,
not replaced by their reduced representatives. Connector words may be arbitrary.
No planar-surface realization or minimal-band theorem is assumed here. -/
namespace TorsionFreeZeroDivisors.AlgebraicPictures
open FreeGroup
variable {A I : Type*} (rel : I → List (A×Bool))

structure Term where
  index : I
  positive : Bool
  connector : List (A×Bool)
namespace Term
variable (t : Term (A:=A) (I:=I))
def core : List (A×Bool) := if t.positive then rel t.index else invRev (rel t.index)
def word : List (A×Bool) := t.connector++t.core rel++invRev t.connector
def flip : Term (A:=A) (I:=I) := ⟨t.index,!t.positive,t.connector⟩
lemma core_flip : t.flip.core rel=invRev (t.core rel) := by
  cases t with
  | mk i b c => cases b <;> simp [flip,core]
lemma word_flip : t.flip.word rel=invRev (t.word rel) := by
  change t.connector++t.flip.core rel++invRev t.connector=_
  rw [core_flip]
  simp only [word,invRev_append,invRev_invRev,List.append_assoc]
end Term

def word (ts : List (Term (A:=A) (I:=I))) : List (A×Bool) := ts.flatMap (Term.word rel)
def relations : Set (FreeGroup A) := Set.range (fun i=>mk (rel i))
lemma word_append (s t : List (Term (A:=A) (I:=I))) :
    word rel (s++t)=word rel s++word rel t := List.flatMap_append
lemma word_reverse_flip (s : List (Term (A:=A) (I:=I))) :
    word rel (s.reverse.map Term.flip)=invRev (word rel s) := by
  induction s with
  | nil => rfl
  | cons t s ih =>
    simp only [List.reverse_cons,List.map_append,List.map_singleton,
      word,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] at *
    rw [ih,Term.word_flip,invRev_append]

lemma term_mem (t : Term (A:=A) (I:=I)) :
    mk (t.word rel)∈Subgroup.normalClosure (relations rel) := by
  have h : mk (t.core rel)∈Subgroup.normalClosure (relations rel) := by
    have hr : mk (rel t.index)∈Subgroup.normalClosure (relations rel) :=
      Subgroup.subset_normalClosure ⟨t.index,rfl⟩
    cases hb : t.positive <;> simp only [Term.core,hb,Bool.false_eq_true,ite_false,ite_true]
    · rw [←inv_mk]
      exact Subgroup.inv_mem _ hr
    · exact hr
  simpa only [Term.word,←mul_mk,←inv_mk] using
    (Subgroup.normalClosure_normal (s:=relations rel)).conj_mem _ h (mk t.connector)

lemma word_mem (s : List (Term (A:=A) (I:=I))) :
    mk (word rel s)∈Subgroup.normalClosure (relations rel) := by
  induction s with
  | nil => exact Subgroup.one_mem _
  | cons t s ih =>
    change mk (t.word rel++word rel s)∈_
    rw [←mul_mk]
    exact Subgroup.mul_mem _ (term_mem rel t) ih

/-- Literal normal-closure expansion, with each actual relator and its sign. -/
theorem expansion {g : FreeGroup A} (h : g∈Subgroup.normalClosure (relations rel)) :
    ∃ ts : List (Term (A:=A) (I:=I)),mk (word rel ts)=g := by
  classical
  induction h using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨r,⟨i,rfl⟩,hc⟩ := Group.mem_conjugatesOfSet_iff.mp hg
    obtain ⟨c,rfl⟩ := isConj_iff.mp hc
    refine ⟨[⟨i,true,c.toWord⟩],?_⟩
    simp only [word,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      Term.word,Term.core,ite_true,←mul_mk,←inv_mk,mk_toWord]
  | one => exact ⟨[],rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s,hs⟩ := hx
    obtain ⟨t,ht⟩ := hy
    exact ⟨s++t,by rw [word_append,←mul_mk,hs,ht]⟩
  | inv x _ hx =>
    obtain ⟨s,hs⟩ := hx
    exact ⟨s.reverse.map Term.flip,by rw [word_reverse_flip,←inv_mk,hs]⟩

variable (outer : List (A×Bool))
def cutWord (ts : List (Term (A:=A) (I:=I))) : List (A×Bool) :=
  invRev outer++word rel ts

/-- A null word in the literal quotient has an actual finite inverse-letter
noncrossing matching after cutting along its conjugating paths. This is the
algebraic cancellation step; it does not assert the later band reduction. -/
theorem quotient_identity (h : PresentedGroup.mk (relations rel) (mk outer)=1) :
    ∃ ts : List (Term (A:=A) (I:=I)),
      Nonempty (WordPairing.Data WordPairing.inverseLetter (cutWord rel outer ts).get) := by
  obtain ⟨ts,ht⟩ := expansion rel (PresentedGroup.mk_eq_one_iff.mp h)
  refine ⟨ts,WordPairing.of_identity ?_⟩
  rw [cutWord,←mul_mk,←inv_mk,ht,inv_mul_cancel]

/-- The empty-relator case is not silently excluded: its boundary must itself
be a free-group identity. -/
lemma empty_relators (h : mk (word rel [])=mk outer) : mk outer=1 := h.symm

end TorsionFreeZeroDivisors.AlgebraicPictures

end

end OAI
