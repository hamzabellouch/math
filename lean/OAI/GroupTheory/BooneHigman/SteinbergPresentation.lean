import OAI.GroupTheory.BooneHigman.AlgebraPresentations

namespace OAI

noncomputable section

/-!
Finite free-algebra Steinberg presentations and transport to finitely presented algebras.
-/

namespace FiniteAlgebraicEnvelopes.SteinbergFiniteFree

section
open scoped commutatorElement
variable {Q : Type*} [Group Q]

theorem commute_commutator {a b c : Q} (hab : Commute a b) (hac : Commute a c) :
    Commute a ⁅b,c⁆ := by
  exact ((hab.mul_right hac).mul_right hab.inv_right).mul_right hac.inv_right

/-- The rank-four commutator calculus needed for the finite free-algebra presentation. -/
theorem associate_commutator (a b c : Q) (hac : Commute a c)
    (hde : Commute ⁅a,b⁆ ⁅b,c⁆) (hec : Commute ⁅b,c⁆ c) :
    ⁅⁅a,b⁆,c⁆=⁅a,⁅b,c⁆⁆ := by
  have h := commutatorElement_commutatorElement_conj_mul a b c
  have hca : c*a*c⁻¹=a := by rw [←hac.eq]; simp [mul_assoc]
  have hbc : b*c*b⁻¹=⁅b,c⁆*c := by simp [commutatorElement_def,mul_assoc]
  rw [hac.symm.commutator_eq,hca,hbc,commutatorElement_one_left,mul_one,
    commutatorElement_mul_right_eq_mul_conj,hde.commutator_eq,one_mul] at h
  have he : Commute ⁅b,c⁆ ⁅⁅a,b⁆,c⁆ := commute_commutator hde.symm hec
  rw [he.eq] at h
  simp only [mul_assoc,mul_inv_cancel,mul_one] at h
  have hh := mul_eq_one_iff_eq_inv.mp h
  simpa only [commutatorElement_inv] using hh

/-- A central commutator of an involution is itself an involution. -/
theorem commutator_square (a b : Q) (ha : a*a=1) (hc : Commute a ⁅a,b⁆) :
    ⁅a,b⁆*⁅a,b⁆=1 := by
  have h := commutatorElement_mul_left_eq_conj_mul a a b
  rw [ha,commutatorElement_one_left,hc.eq] at h
  simpa only [mul_assoc,mul_inv_cancel,one_mul,mul_one] using h.symm

end

open scoped commutatorElement
variable {A Q : Type*} [Group Q]

structure SmallSystem (A Q : Type*) [Group Q] where
  small : Fin 6 → Fin 6 → Option A → Q
  diagonal : ∀ i a, small i i a=1
  square : ∀ i j a, small i j a*small i j a=1
  distant : ∀ i j k l a b, i≠l → j≠k → Commute (small i j a) (small k l b)
  unit_left : ∀ i j k a, i≠j → j≠k → i≠k → ⁅small i j none,small j k a⁆=small i k a
  unit_right : ∀ i j k a, i≠j → j≠k → i≠k → ⁅small i j a,small j k none⁆=small i k a

lemma freshIndex (s : Finset (Fin 6)) (hs : s.card<6) : ∃ i : Fin 6, i∉s := by
  have h := Finset.exists_mem_notMem_of_card_lt_card (s:=s) (t:=Finset.univ)
    (by simpa using hs)
  simpa using h

lemma fresh5 (a b c d e : Fin 6) : ∃ i : Fin 6, i≠a ∧ i≠b ∧ i≠c ∧ i≠d ∧ i≠e := by
  have hc : ({a,b,c,d,e} : Finset (Fin 6)).card≤5 := by
    have h1 := Finset.card_insert_le a ({b,c,d,e} : Finset (Fin 6))
    have h2 := Finset.card_insert_le b ({c,d,e} : Finset (Fin 6))
    have h3 := Finset.card_insert_le c ({d,e} : Finset (Fin 6))
    have h4 := Finset.card_insert_le d ({e} : Finset (Fin 6))
    simp only [Finset.card_singleton] at h4
    omega
  simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using
    freshIndex {a,b,c,d,e} (by omega)

def middle (i j : Fin 6) : Fin 6 := (fresh5 i j j j j).choose
lemma middle_ne_left (i j : Fin 6) : middle i j≠i := (fresh5 i j j j j).choose_spec.1
lemma middle_ne_right (i j : Fin 6) : middle i j≠j := (fresh5 i j j j j).choose_spec.2.1

namespace SmallSystem
variable (S : SmallSystem A Q)

def word : List A → Fin 6 → Fin 6 → Q
  | [],i,j => S.small i j none
  | [a],i,j => S.small i j (some a)
  | a::b::w,i,j => if i=j then 1 else ⁅S.small i (middle i j) (some a),word (b::w) (middle i j) j⁆

@[simp] lemma word_nil (i j : Fin 6) : S.word [] i j=S.small i j none := rfl
@[simp] lemma word_singleton (a : A) (i j : Fin 6) : S.word [a] i j=S.small i j (some a) := rfl
@[simp] lemma word_diagonal (w : List A) (i : Fin 6) : S.word w i i=1 := by
  cases w with
  | nil => exact S.diagonal i none
  | cons a w => cases w <;> simp [word,S.diagonal]

lemma word_cons {w : List A} (hw : w≠[]) (a : A) (i j : Fin 6) (hij : i≠j) :
    S.word (a::w) i j=⁅S.small i (middle i j) (some a),S.word w (middle i j) j⁆ := by
  cases w with
  | nil => contradiction
  | cons b w => simp [word,hij]

/-- Finite-length invariants for the simultaneous noncommutative-root induction.
The distant invariant bounds the maximum, not the sum, of the two word lengths. -/
structure Valid (n : ℕ) : Prop where
  factor : ∀ (a : A) (w : List A), w≠[] → (a::w).length≤n →
    ∀ i k j : Fin 6, i≠k → k≠j → i≠j → S.word (a::w) i j=⁅S.small i k (some a),S.word w k j⁆
  distant : ∀ (w v : List A), w.length≤n → v.length≤n →
    ∀ i j k l : Fin 6, i≠l → j≠k → Commute (S.word w i j) (S.word v k l)
  chain : ∀ (w v : List A), w.length+v.length≤n →
    ∀ i j k : Fin 6, i≠j → j≠k → i≠k → ⁅S.word w i j,S.word v j k⁆=S.word (w++v) i k
  square : ∀ (w : List A), w.length≤n → ∀ i j : Fin 6, S.word w i j*S.word w i j=1

lemma valid_zero : S.Valid 0 := by
  constructor
  · intro a w hw hn; simp at hn
  · intro w v hw hv
    have : w=[] := List.length_eq_zero_iff.mp (by omega)
    have : v=[] := List.length_eq_zero_iff.mp (by omega)
    subst w; subst v
    exact fun i j k l h1 h2 => S.distant i j k l none none h1 h2
  · intro w v hw
    have : w=[] := List.length_eq_zero_iff.mp (by omega)
    have : v=[] := List.length_eq_zero_iff.mp (by omega)
    subst w; subst v
    exact fun i j k hij hjk hik => S.unit_left i j k none hij hjk hik
  · intro w hw
    have : w=[] := List.length_eq_zero_iff.mp (by omega)
    subst w
    exact fun i j => S.square i j none

lemma factor_step {n : ℕ} (H : S.Valid n) (a : A) (w : List A) (hw : w≠[])
    (hn : (a::w).length≤n+1) (i k j : Fin 6) (hik : i≠k) (hkj : k≠j) (hij : i≠j) :
    S.word (a::w) i j=⁅S.small i k (some a),S.word w k j⁆ := by
  have hwlen : w.length≤n := by simpa using hn
  have h1 : 1≤n := by have := List.length_pos_iff.mpr hw; omega
  let p := middle i j
  have hpi : p≠i := middle_ne_left i j
  have hpj : p≠j := middle_ne_right i j
  rw [S.word_cons hw a i j hij]
  by_cases hpk : p=k
  · subst k; rfl
  have hleft := S.unit_right i k p (some a) hik (Ne.symm hpk) hpi.symm
  have hright := H.chain [] w (by simpa using hwlen) k p j (Ne.symm hpk) hpj hkj
  simp only [word_nil,List.nil_append] at hright
  have hac : Commute (S.small i k (some a)) (S.word w p j) :=
    H.distant [a] w (by simpa using h1) hwlen i k p j hij (Ne.symm hpk)
  have hd : Commute (S.small i p (some a)) (S.word w k j) :=
    H.distant [a] w (by simpa using h1) hwlen i p k j hij hpk
  have hc : Commute (S.word w k j) (S.word w p j) :=
    H.distant w w hwlen hwlen k j p j hkj hpj.symm
  have hh := associate_commutator (S.small i k (some a)) (S.small k p none) (S.word w p j) hac
    (by rw [hleft,hright]; exact hd) (by rw [hright]; exact hc)
  rw [hleft,hright] at hh
  exact hh

end SmallSystem
end FiniteAlgebraicEnvelopes.SteinbergFiniteFree

namespace FiniteAlgebraicEnvelopes.SteinbergFiniteFree.SmallSystem

section
open scoped commutatorElement
variable {A Q : Type*} [Group Q] (S : SmallSystem A Q)

lemma short_word (w : List A) (hw : w.length≤1) : ∃ a : Option A, w=a.toList := by
  cases w with
  | nil => exact ⟨none,rfl⟩
  | cons a w =>
    have : w=[] := List.length_eq_zero_iff.mp (by simpa using hw)
    subst w
    exact ⟨some a,rfl⟩

@[simp] lemma word_option (a : Option A) (i j : Fin 6) : S.word a.toList i j=S.small i j a := by
  cases a <;> rfl

lemma valid_one : S.Valid 1 := by
  constructor
  · intro a w hw hn
    have hp := List.length_pos_iff.mpr hw
    simp only [List.length_cons] at hn
    omega
  · intro w v hw hv
    obtain ⟨a,rfl⟩ := short_word w hw
    obtain ⟨b,rfl⟩ := short_word v hv
    simpa only [word_option] using fun i j k l h1 h2 => S.distant i j k l a b h1 h2
  · intro w v hw
    obtain ⟨a,rfl⟩ := short_word w (by omega)
    obtain ⟨b,rfl⟩ := short_word v (by omega)
    cases a with
    | none => simpa using S.unit_left (a:=b)
    | some a =>
      cases b with
      | none => simpa using S.unit_right (a:=some a)
      | some b => simp at hw
  · intro w hw
    obtain ⟨a,rfl⟩ := short_word w hw
    simpa using fun i j => S.square i j a

lemma distant_step_short {n : ℕ} (hn : 1≤n) (H : S.Valid n)
    (w v : List A) (hw : w.length≤n+1) (hv : v.length≤n)
    (i j k l : Fin 6) (hil : i≠l) (hjk : j≠k) :
    Commute (S.word w i j) (S.word v k l) := by
  by_cases hij : i=j
  · subst j; rw [word_diagonal]; exact Commute.one_left _
  cases w with
  | nil => exact H.distant [] v (by simp) hv i j k l hil hjk
  | cons a w =>
    cases w with
    | nil => exact H.distant [a] v (by simpa using hn) hv i j k l hil hjk
    | cons b w =>
      obtain ⟨p,hpi,hpj,hpk,hpl,_⟩ := fresh5 i j k l l
      rw [S.factor_step H a (b::w) (by simp) hw i p j hpi.symm hpj hij]
      exact (commute_commutator
        (H.distant [a] v (by simpa using hn) hv i p k l hil hpk).symm
        (H.distant (b::w) v (by simpa using hw) hv p j k l hpl hjk).symm).symm

lemma distant_step {n : ℕ} (hn : 1≤n) (H : S.Valid n)
    (w v : List A) (hw : w.length≤n+1) (hv : v.length≤n+1)
    (i j k l : Fin 6) (hil : i≠l) (hjk : j≠k) :
    Commute (S.word w i j) (S.word v k l) := by
  by_cases hvo : v.length≤n
  · exact S.distant_step_short hn H w v hw hvo i j k l hil hjk
  by_cases hwo : w.length≤n
  · exact (S.distant_step_short hn H v w hv hwo k l i j hjk.symm hil.symm).symm
  by_cases hij : i=j
  · subst j; rw [word_diagonal]; exact Commute.one_left _
  by_cases hkl : k=l
  · subst l; rw [word_diagonal]; exact Commute.one_right _
  cases w with
  | nil => simp at hwo
  | cons a w =>
    cases w with
    | nil => simp at hwo; omega
    | cons b w =>
      cases v with
      | nil => simp at hvo
      | cons c v =>
        cases v with
        | nil => simp at hvo; omega
        | cons d v =>
          obtain ⟨p,hpi,hpj,hpk,hpl,_⟩ := fresh5 i j k l l
          obtain ⟨q,hqi,hqj,hqk,hql,hqp⟩ := fresh5 i j k l p
          rw [S.factor_step H a (b::w) (by simp) hw i p j hpi.symm hpj hij,
            S.factor_step H c (d::v) (by simp) hv k q l hqk.symm hql hkl]
          have h1 := H.distant [a] [c] (by simpa using hn) (by simpa using hn) i p k q hqi.symm hpk
          have h2 := H.distant [a] (d::v) (by simpa using hn) (by simpa using hv) i p q l hil hqp.symm
          have h3 := H.distant (b::w) [c] (by simpa using hw) (by simpa using hn) p j k q hqp.symm hjk
          have h4 := H.distant (b::w) (d::v) (by simpa using hw) (by simpa using hv) p j q l hpl hqj.symm
          exact (commute_commutator (commute_commutator h1 h2).symm
            (commute_commutator h3 h4).symm).symm

lemma chain_step {n : ℕ} (hn : 1≤n) (H : S.Valid n)
    (w v : List A) (hw : w.length+v.length≤n+1)
    (i j k : Fin 6) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅S.word w i j,S.word v j k⁆=S.word (w++v) i k := by
  have hw' : w.length≤n+1 := by omega
  have hv' : v.length≤n+1 := by omega
  cases w with
  | nil =>
    cases v with
    | nil => exact S.unit_left i j k none hij hjk hik
    | cons a v =>
      cases v with
      | nil => exact S.unit_left i j k (some a) hij hjk hik
      | cons b v =>
        obtain ⟨p,hpi,hpj,hpk,_,_⟩ := fresh5 i j k k k
        have hfac := S.factor_step H a (b::v) (by simp) hv' j p k hpj.symm hpk hjk
        have hleft := S.unit_left i j p (some a) hij hpj.symm hpi.symm
        have hfac' := S.factor_step H a (b::v) (by simp) hv' i p k hpi.symm hpk hik
        have hac : Commute (S.word [] i j) (S.word (b::v) p k) :=
          S.distant_step hn H [] (b::v) (by simp) (by simp only [List.length_cons, List.length_nil] at *; omega) i j p k hik hpj.symm
        have hd : Commute (S.word [a] i p) (S.word (a::b::v) j k) :=
          S.distant_step hn H [a] (a::b::v) (by simp only [List.length_cons, List.length_nil]; omega) hv' i p j k hik hpj
        have hc : Commute (S.word (a::b::v) j k) (S.word (b::v) p k) :=
          S.distant_step hn H (a::b::v) (b::v) hv' (by simp only [List.length_cons, List.length_nil] at *; omega) j k p k hjk hpk.symm
        have hh := associate_commutator (S.small i j none) (S.small j p (some a))
          (S.word (b::v) p k) hac (by rw [hleft,←hfac]; exact hd)
          (by rw [←hfac]; exact hc)
        rw [hleft,←hfac,←hfac'] at hh
        exact hh.symm
  | cons a w =>
    cases w with
    | nil =>
      cases v with
      | nil => exact S.unit_right i j k (some a) hij hjk hik
      | cons b v =>
        simpa using (S.factor_step H a (b::v) (by simp) (by simp only [List.length_cons, List.length_nil] at *; omega) i j k hij hjk hik).symm
    | cons b w =>
      obtain ⟨p,hpi,hpj,hpk,_,_⟩ := fresh5 i j k k k
      have hfac := S.factor_step H a (b::w) (by simp) hw' i p j hpi.symm hpj hij
      have hsum : (b::w).length+v.length≤n := by simp only [List.length_cons] at *; omega
      have hright := H.chain (b::w) v hsum p j k hpj hjk hpk
      have hfac' := S.factor_step H a ((b::w)++v) (by simp) (by simp only [List.length_cons, List.length_append] at *; omega) i p k hpi.symm hpk hik
      have hac : Commute (S.word [a] i p) (S.word v j k) :=
        S.distant_step hn H [a] v (by simp only [List.length_cons, List.length_nil]; omega) hv' i p j k hik hpj
      have hd : Commute (S.word (a::b::w) i j) (S.word ((b::w)++v) p k) :=
        S.distant_step hn H (a::b::w) ((b::w)++v) hw' (by simp only [List.length_cons, List.length_append] at *; omega) i j p k hik hpj.symm
      have hc : Commute (S.word ((b::w)++v) p k) (S.word v j k) :=
        S.distant_step hn H ((b::w)++v) v (by simp only [List.length_cons, List.length_append] at *; omega) hv' p k j k hpk hjk.symm
      have hh := associate_commutator (S.small i p (some a)) (S.word (b::w) p j) (S.word v j k)
        hac (by rw [←hfac,hright]; exact hd) (by rw [hright]; exact hc)
      rw [←hfac,hright,←hfac'] at hh
      exact hh

lemma square_step {n : ℕ} (hn : 1≤n) (H : S.Valid n)
    (w : List A) (hw : w.length≤n+1) (i j : Fin 6) : S.word w i j*S.word w i j=1 := by
  by_cases hij : i=j
  · subst j; simp
  cases w with
  | nil => exact S.square i j none
  | cons a w =>
    cases w with
    | nil => exact S.square i j (some a)
    | cons b w =>
      let p := middle i j
      have hpi : p≠i := middle_ne_left i j
      have hpj : p≠j := middle_ne_right i j
      have hf := S.factor_step H a (b::w) (by simp) hw i p j hpi.symm hpj hij
      rw [hf]
      exact commutator_square _ _ (S.square i p (some a)) (by
        rw [←hf]
        exact S.distant_step hn H [a] (a::b::w) (by simp only [List.length_cons, List.length_nil]; omega) hw i p i j hij hpi)

lemma valid_succ {n : ℕ} (hn : 1≤n) (H : S.Valid n) : S.Valid (n+1) where
  factor := S.factor_step H
  distant := S.distant_step hn H
  chain := S.chain_step hn H
  square := S.square_step hn H

lemma valid (n : ℕ) : S.Valid n := by
  induction n with
  | zero => exact S.valid_zero
  | succ n ih =>
    by_cases hn : n=0
    · subst n; exact S.valid_one
    · exact S.valid_succ (by omega) ih

lemma word_distant (w v : List A) (i j k l : Fin 6) (hil : i≠l) (hjk : j≠k) :
    Commute (S.word w i j) (S.word v k l) :=
  (S.valid (w.length+v.length)).distant w v (by omega) (by omega) i j k l hil hjk

lemma word_chain (w v : List A) (i j k : Fin 6) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅S.word w i j,S.word v j k⁆=S.word (w++v) i k :=
  (S.valid (w.length+v.length)).chain w v (by omega) i j k hij hjk hik

lemma word_square (w : List A) (i j : Fin 6) : S.word w i j*S.word w i j=1 :=
  (S.valid w.length).square w (by omega) i j

end

open scoped commutatorElement IsMulCommutative
variable {A Q : Type*} [Group Q] (S : SmallSystem A Q)

abbrev Polynomial (A : Type*) := MonoidAlgebra (ZMod 2) (FreeMonoid A)

def rootSubgroup (i j : Fin 6) : Subgroup Q := Subgroup.closure (Set.range fun w => S.word w i j)
instance root_commutative (i j : Fin 6) : IsMulCommutative (S.rootSubgroup i j) := by
  apply Subgroup.isMulCommutative_closure
  rintro _ ⟨w,rfl⟩ _ ⟨v,rfl⟩ _
  by_cases hij : i=j
  · subst j; simp
  · exact (S.word_distant w v i j i j hij (Ne.symm hij)).eq

def wordInRoot (w : List A) (i j : Fin 6) : S.rootSubgroup i j :=
  ⟨S.word w i j,Subgroup.subset_closure ⟨w,rfl⟩⟩

lemma scalar_cases (c : ZMod 2) : c=0 ∨ c=1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

def wordScalar (w : List A) (i j : Fin 6) : ZMod 2 →+ Additive (S.rootSubgroup i j) where
  toFun c := if c=0 then 0 else Additive.ofMul (S.wordInRoot w i j)
  map_zero' := by simp
  map_add' c d := by
    rcases scalar_cases c with rfl|rfl <;> rcases scalar_cases d with rfl|rfl <;>
      simp only [zero_add,add_zero,ite_true,one_ne_zero,ite_false,show (1 : ZMod 2)+1=0 from by decide]
    change (1 : S.rootSubgroup i j)=S.wordInRoot w i j*S.wordInRoot w i j
    apply Subtype.ext
    exact (S.word_square w i j).symm

def polynomialAdd (i j : Fin 6) : Polynomial A →+ Additive (S.rootSubgroup i j) :=
  (Finsupp.liftAddHom fun w : FreeMonoid A => S.wordScalar w.toList i j).comp
    (MonoidAlgebra.coeffAddEquiv (R:=ZMod 2) (M:=FreeMonoid A)).toAddMonoidHom

def polynomial (p : Polynomial A) (i j : Fin 6) : Q :=
  (Additive.toMul (S.polynomialAdd i j p)).val

@[simp] lemma polynomial_zero (i j : Fin 6) : S.polynomial 0 i j=1 := by
  simp [polynomial]

lemma polynomial_add (p q : Polynomial A) (i j : Fin 6) :
    S.polynomial (p+q) i j=S.polynomial p i j*S.polynomial q i j := by
  simp [polynomial]

@[simp] lemma polynomial_single (w : FreeMonoid A) (i j : Fin 6) :
    S.polynomial (MonoidAlgebra.single w 1) i j=S.word w.toList i j := by
  simp [polynomial,polynomialAdd,Finsupp.liftAddHom,wordScalar,wordInRoot]

lemma polynomial_induction (P : Polynomial A → Prop) (h0 : P 0)
    (hword : ∀ w : FreeMonoid A, P (MonoidAlgebra.single w 1))
    (hadd : ∀ p q, P p → P q → P (p+q)) (p : Polynomial A) : P p := by
  apply MonoidAlgebra.induction_on p hword hadd
  intro c p hp
  rcases scalar_cases c with rfl|rfl
  · simpa using h0
  · simpa using hp

lemma polynomial_distant (p q : Polynomial A) (i j k l : Fin 6) (hil : i≠l) (hjk : j≠k) :
    Commute (S.polynomial p i j) (S.polynomial q k l) := by
  apply polynomial_induction (fun p => Commute (S.polynomial p i j) (S.polynomial q k l))
  · simp
  · intro w
    apply polynomial_induction (fun q => Commute (S.polynomial (MonoidAlgebra.single w 1) i j) (S.polynomial q k l))
    · simp
    · intro v; simp only [polynomial_single]; exact S.word_distant _ _ _ _ _ _ hil hjk
    · intro p q hp hq; rw [polynomial_add]; exact hp.mul_right hq
  · intro p q hp hq; rw [polynomial_add]; exact hp.mul_left hq

lemma polynomial_diagonal (p : Polynomial A) (i : Fin 6) : S.polynomial p i i=1 := by
  apply polynomial_induction (fun p => S.polynomial p i i=1)
  · simp
  · intro w; simp
  · intro p q hp hq; rw [polynomial_add,hp,hq,mul_one]

lemma polynomial_chain_add_left (p q r : Polynomial A) (i j k : Fin 6)
    (hij : i≠j) (hik : i≠k)
    (hp : ⁅S.polynomial p i j,S.polynomial r j k⁆=S.polynomial (p*r) i k)
    (hq : ⁅S.polynomial q i j,S.polynomial r j k⁆=S.polynomial (q*r) i k) :
    ⁅S.polynomial (p+q) i j,S.polynomial r j k⁆=S.polynomial ((p+q)*r) i k := by
  rw [polynomial_add,commutatorElement_mul_left_eq_conj_mul,hp,hq]
  rw [(S.polynomial_distant p (q*r) i j i k hik (Ne.symm hij)).eq]
  simp only [mul_assoc,mul_inv_cancel,mul_one]
  rw [add_mul,polynomial_add]
  exact (S.polynomial_distant (q*r) (p*r) i k i k hik (Ne.symm hik)).eq

lemma polynomial_chain_add_right (p q r : Polynomial A) (i j k : Fin 6)
    (hjk : j≠k) (hik : i≠k)
    (hq : ⁅S.polynomial p i j,S.polynomial q j k⁆=S.polynomial (p*q) i k)
    (hr : ⁅S.polynomial p i j,S.polynomial r j k⁆=S.polynomial (p*r) i k) :
    ⁅S.polynomial p i j,S.polynomial (q+r) j k⁆=S.polynomial (p*(q+r)) i k := by
  rw [polynomial_add,commutatorElement_mul_right_eq_mul_conj,hq,hr]
  rw [mul_assoc (S.polynomial (p*q) i k)]
  rw [(S.polynomial_distant q (p*r) j k i k hjk (Ne.symm hik)).eq]
  simp only [mul_assoc,mul_inv_cancel,mul_one]
  rw [mul_add,polynomial_add]

lemma polynomial_chain (p q : Polynomial A) (i j k : Fin 6)
    (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅S.polynomial p i j,S.polynomial q j k⁆=S.polynomial (p*q) i k := by
  apply polynomial_induction (fun p => ⁅S.polynomial p i j,S.polynomial q j k⁆=S.polynomial (p*q) i k)
  · simp
  · intro w
    apply polynomial_induction (fun q => ⁅S.polynomial (MonoidAlgebra.single w 1) i j,S.polynomial q j k⁆=
      S.polynomial (MonoidAlgebra.single w 1*q) i k)
    · simp
    · intro v
      simp only [MonoidAlgebra.single_mul_single,one_mul,polynomial_single,FreeMonoid.toList_mul]
      exact S.word_chain _ _ _ _ _ hij hjk hik
    · intro p q hp hq
      exact S.polynomial_chain_add_right _ _ _ i j k hjk hik hp hq
  · intro p q hp hq
    exact S.polynomial_chain_add_left _ _ _ i j k hij hik hp hq

end FiniteAlgebraicEnvelopes.SteinbergFiniteFree.SmallSystem

namespace FiniteAlgebraicEnvelopes.SteinbergFiniteFree

section
open scoped commutatorElement
variable (A : Type*)
abbrev SmallGenerator := (Fin 6 × Fin 6) × Option A

def freeSmall (i j : Fin 6) (a : Option A) : FreeGroup (SmallGenerator A) := FreeGroup.of ((i,j),a)

def smallRelator (d : Fin 5) (i j k l : Fin 6) (a b : Option A) : FreeGroup (SmallGenerator A) :=
  if d=0 then freeSmall A i i a else
  if d=1 then freeSmall A i j a*freeSmall A i j a else
  if d=2 then if i≠l ∧ j≠k then ⁅freeSmall A i j a,freeSmall A k l b⁆ else 1 else
  if d=3 then if i≠j ∧ j≠k ∧ i≠k then
    ⁅freeSmall A i j none,freeSmall A j k a⁆*(freeSmall A i k a)⁻¹ else 1 else
  if i≠j ∧ j≠k ∧ i≠k then
    ⁅freeSmall A i j a,freeSmall A j k none⁆*(freeSmall A i k a)⁻¹ else 1

def smallRelations : Set (FreeGroup (SmallGenerator A)) :=
  Set.range fun z : Fin 5 × Fin 6 × Fin 6 × Fin 6 × Fin 6 × Option A × Option A =>
    smallRelator A z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2

abbrev Presentation := PresentedGroup (smallRelations A)
instance [Finite A] : Group.IsFinitelyPresented (Presentation A) := by
  have : Finite (smallRelations A) := (Set.finite_range _).to_subtype
  infer_instance

def presentSmall (i j : Fin 6) (a : Option A) : Presentation A := PresentedGroup.of ((i,j),a)
lemma present_relator (d : Fin 5) (i j k l : Fin 6) (a b : Option A) :
    PresentedGroup.mk (smallRelations A) (smallRelator A d i j k l a b)=1 :=
  PresentedGroup.one_of_mem (rels:=smallRelations A) ⟨(d,i,j,k,l,a,b),rfl⟩

lemma present_diagonal (i : Fin 6) (a : Option A) : presentSmall A i i a=1 := by
  simpa [smallRelator,freeSmall,presentSmall,PresentedGroup.of] using present_relator A 0 i i i i a a
lemma present_square (i j : Fin 6) (a : Option A) : presentSmall A i j a*presentSmall A i j a=1 := by
  simpa [smallRelator,freeSmall,presentSmall,PresentedGroup.of] using present_relator A 1 i j i j a a
lemma present_distant (i j k l : Fin 6) (a b : Option A) (hil : i≠l) (hjk : j≠k) :
    Commute (presentSmall A i j a) (presentSmall A k l b) := by
  apply commutatorElement_eq_one_iff_mul_comm.mp
  simpa [smallRelator,freeSmall,presentSmall,PresentedGroup.of,hil,hjk] using present_relator A 2 i j k l a b
lemma present_unit_left (i j k : Fin 6) (a : Option A) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅presentSmall A i j none,presentSmall A j k a⁆=presentSmall A i k a := by
  apply mul_inv_eq_one.mp
  simpa [smallRelator,freeSmall,presentSmall,PresentedGroup.of,hij,hjk,hik] using present_relator A 3 i j k k a a
lemma present_unit_right (i j k : Fin 6) (a : Option A) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅presentSmall A i j a,presentSmall A j k none⁆=presentSmall A i k a := by
  apply mul_inv_eq_one.mp
  simpa [smallRelator,freeSmall,presentSmall,PresentedGroup.of,hij,hjk,hik] using present_relator A 4 i j k k a a

def presentSystem : SmallSystem A (Presentation A) where
  small := presentSmall A
  diagonal := present_diagonal A
  square := present_square A
  distant := present_distant A
  unit_left := present_unit_left A
  unit_right := present_unit_right A

variable {A} {Q : Type*} [Group Q] (S : SmallSystem A Q)
def SmallSystem.fromPresentation : Presentation A →* Q :=
  PresentedGroup.toGroup (f:=fun z : SmallGenerator A => S.small z.1.1 z.1.2 z.2) (by
    rintro _ ⟨⟨d,i,j,k,l,a,b⟩,rfl⟩
    simp only [smallRelator]
    split_ifs <;> simp_all only [map_mul,map_inv,map_commutatorElement,map_one,freeSmall,FreeGroup.lift_apply_of]
    all_goals first
      | exact S.diagonal _ _
      | exact S.square _ _ _
      | exact (S.distant _ _ _ _ _ _ (by tauto) (by tauto)).commutator_eq
      | rw [S.unit_left _ _ _ _ (by tauto) (by tauto) (by tauto),mul_inv_cancel]
      | rw [S.unit_right _ _ _ _ (by tauto) (by tauto) (by tauto),mul_inv_cancel])

@[simp] lemma SmallSystem.fromPresentation_small (i j : Fin 6) (a : Option A) :
    S.fromPresentation (presentSmall A i j a)=S.small i j a := PresentedGroup.toGroup.of _

end

section
open scoped commutatorElement
open SmallSystem
variable {A Q Q' : Type*} [Group Q] [Group Q']
variable (S : SmallSystem A Q) (T : SmallSystem A Q') (f : Q →* Q')
variable (hf : ∀ i j a, f (S.small i j a)=T.small i j a)

include hf in
lemma SmallSystem.map_word (w : List A) (i j : Fin 6) : f (S.word w i j)=T.word w i j := by
  induction w generalizing i j with
  | nil => exact hf i j none
  | cons a w ih =>
    cases w with
    | nil => exact hf i j (some a)
    | cons b w =>
      by_cases hij : i=j
      · subst j; simp
      · rw [S.word_cons (by simp) a i j hij,T.word_cons (by simp) a i j hij,map_commutatorElement,hf]
        exact congrArg (fun z => ⁅T.small i (middle i j) (some a),z⁆) (by
          exact ih (middle i j) j)

include hf in
lemma SmallSystem.map_polynomial (p : Polynomial A) (i j : Fin 6) :
    f (S.polynomial p i j)=T.polynomial p i j := by
  apply polynomial_induction (fun p => f (S.polynomial p i j)=T.polynomial p i j)
  · simp
  · intro w; simp only [polynomial_single]; exact S.map_word T f hf _ i j
  · intro p q hp hq; rw [S.polynomial_add,T.polynomial_add,map_mul,hp,hq]

variable (A : Type*)
def polynomialBackward : Steinberg.Group (Fin 6) (Polynomial A) →* Presentation A :=
  PresentedGroup.toGroup (f:=fun z : Steinberg.Generator (Fin 6) (Polynomial A) =>
    (presentSystem A).polynomial z.2 z.1.1.1 z.1.1.2) (by
    intro w hw
    cases hw with
    | additive i j hij a b =>
      simp only [map_mul,map_inv,Steinberg.freeRoot,FreeGroup.lift_apply_of]
      rw [←SmallSystem.polynomial_add,mul_inv_cancel]
    | chain i j k hij hjk hik a b =>
      simp only [map_mul,map_inv,map_commutatorElement,Steinberg.freeRoot,FreeGroup.lift_apply_of]
      rw [SmallSystem.polynomial_chain _ a b i j k hij hjk hik,mul_inv_cancel]
    | distant i j k l hij hkl hil hjk a b =>
      simp only [map_commutatorElement,Steinberg.freeRoot,FreeGroup.lift_apply_of]
      exact (SmallSystem.polynomial_distant _ a b i j k l hil hjk).commutator_eq)

@[simp] lemma polynomialBackward_root (i j : Fin 6) (hij : i≠j) (p : Polynomial A) :
    polynomialBackward A (Steinberg.root i j hij p)=(presentSystem A).polynomial p i j :=
  PresentedGroup.toGroup.of _

end

open scoped commutatorElement
open SmallSystem
variable (A : Type*)

def actualSmall (i j : Fin 6) (a : Option A) : Steinberg.Group (Fin 6) (Polynomial A) :=
  if hij : i=j then 1 else Steinberg.root i j hij (MonoidAlgebra.single (FreeMonoid.ofList a.toList) 1)

@[simp] lemma actualSmall_diagonal (i : Fin 6) (a : Option A) : actualSmall A i i a=1 := by simp [actualSmall]
lemma actualSmall_off (i j : Fin 6) (hij : i≠j) (a : Option A) :
    actualSmall A i j a=Steinberg.root i j hij (MonoidAlgebra.single (FreeMonoid.ofList a.toList) 1) := by
  simp [actualSmall,hij]

lemma actualSmall_square (i j : Fin 6) (a : Option A) : actualSmall A i j a*actualSmall A i j a=1 := by
  by_cases hij : i=j
  · subst j; simp
  · rw [actualSmall_off A i j hij a,Steinberg.root_add,←MonoidAlgebra.single_add,show (1 : ZMod 2)+1=0 from by decide,
      MonoidAlgebra.single_zero,Steinberg.root_zero]

lemma actualSmall_distant (i j k l : Fin 6) (a b : Option A) (hil : i≠l) (hjk : j≠k) :
    Commute (actualSmall A i j a) (actualSmall A k l b) := by
  by_cases hij : i=j
  · subst j; simp
  by_cases hkl : k=l
  · subst l; simp
  rw [actualSmall_off A i j hij a,actualSmall_off A k l hkl b]
  exact Steinberg.root_distant i j k l hij hkl hil hjk _ _

lemma actualSmall_unit_left (i j k : Fin 6) (a : Option A) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅actualSmall A i j none,actualSmall A j k a⁆=actualSmall A i k a := by
  rw [actualSmall_off A i j hij,actualSmall_off A j k hjk,actualSmall_off A i k hik,
    Steinberg.root_chain i j k hij hjk hik]
  simp only [Option.toList_none,FreeMonoid.ofList_nil,←MonoidAlgebra.one_def,one_mul]

lemma actualSmall_unit_right (i j k : Fin 6) (a : Option A) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅actualSmall A i j a,actualSmall A j k none⁆=actualSmall A i k a := by
  rw [actualSmall_off A i j hij,actualSmall_off A j k hjk,actualSmall_off A i k hik,
    Steinberg.root_chain i j k hij hjk hik]
  simp only [Option.toList_none,FreeMonoid.ofList_nil,←MonoidAlgebra.one_def,mul_one]

def actualSystem : SmallSystem A (Steinberg.Group (Fin 6) (Polynomial A)) where
  small := actualSmall A
  diagonal := actualSmall_diagonal A
  square := actualSmall_square A
  distant := actualSmall_distant A
  unit_left := actualSmall_unit_left A
  unit_right := actualSmall_unit_right A

lemma actual_word (w : List A) (i j : Fin 6) (hij : i≠j) :
    (actualSystem A).word w i j=Steinberg.root i j hij (MonoidAlgebra.single (FreeMonoid.ofList w) 1) := by
  induction w generalizing i j with
  | nil => exact actualSmall_off A i j hij none
  | cons a w ih =>
    cases w with
    | nil => exact actualSmall_off A i j hij (some a)
    | cons b w =>
      have hmi := middle_ne_left i j
      have hmj := middle_ne_right i j
      rw [SmallSystem.word_cons _ (by simp) a i j hij]
      change ⁅actualSmall A i (middle i j) (some a),_⁆=_
      rw [actualSmall_off A i (middle i j) (Ne.symm hmi),ih _ j hmj,
        Steinberg.root_chain i (middle i j) j (Ne.symm hmi) hmj hij,
        MonoidAlgebra.single_mul_single,one_mul]
      rfl

lemma actual_polynomial (p : Polynomial A) (i j : Fin 6) (hij : i≠j) :
    (actualSystem A).polynomial p i j=Steinberg.root i j hij p := by
  apply polynomial_induction (fun p => (actualSystem A).polynomial p i j=Steinberg.root i j hij p)
  · simp
  · intro w
    rw [SmallSystem.polynomial_single,actual_word A _ i j hij,FreeMonoid.ofList_toList]
  · intro p q hp hq
    rw [SmallSystem.polynomial_add,hp,hq,Steinberg.root_add]

def polynomialForward : Presentation A →* Steinberg.Group (Fin 6) (Polynomial A) :=
  (actualSystem A).fromPresentation

lemma polynomial_forward_backward :
    (polynomialForward A).comp (polynomialBackward A)=MonoidHom.id _ := by
  apply PresentedGroup.ext
  rintro ⟨⟨⟨i,j⟩,hij⟩,p⟩
  change polynomialForward A (polynomialBackward A (Steinberg.root i j hij p))=Steinberg.root i j hij p
  rw [polynomialBackward_root]
  rw [SmallSystem.map_polynomial (presentSystem A) (actualSystem A) (polynomialForward A)
    (fun i j a => (actualSystem A).fromPresentation_small i j a),actual_polynomial A p i j hij]

lemma polynomial_backward_forward :
    (polynomialBackward A).comp (polynomialForward A)=MonoidHom.id _ := by
  apply PresentedGroup.ext
  rintro ⟨⟨i,j⟩,a⟩
  change polynomialBackward A (polynomialForward A (presentSmall A i j a))=presentSmall A i j a
  change polynomialBackward A ((actualSystem A).fromPresentation (presentSmall A i j a))=_
  rw [SmallSystem.fromPresentation_small]
  change polynomialBackward A (actualSmall A i j a)=_
  by_cases hij : i=j
  · subst j; simp only [actualSmall_diagonal,map_one,present_diagonal]
  · rw [actualSmall_off A i j hij,polynomialBackward_root,SmallSystem.polynomial_single]
    simp only [FreeMonoid.toList_ofList,SmallSystem.word_option]
    rfl

def polynomialEquivalence : Presentation A ≃* Steinberg.Group (Fin 6) (Polynomial A) :=
  { polynomialForward A with
    invFun := polynomialBackward A
    left_inv := DFunLike.congr_fun (polynomial_backward_forward A)
    right_inv := DFunLike.congr_fun (polynomial_forward_backward A) }

instance polynomial_finitelyPresented [Finite A] : Group.IsFinitelyPresented (Steinberg.Group (Fin 6) (Polynomial A)) :=
  Group.IsFinitelyPresented.equiv (polynomialEquivalence A)

/-- A finite rank-six presentation for the noncommutative free algebra over F₂.
All long-word and additive Steinberg relations follow from the finite small-root relations. -/
instance freeAlgebra_finitelyPresented [Finite A] :
    Group.IsFinitelyPresented (Steinberg.Group (Fin 6) (FreeAlgebra (ZMod 2) A)) :=
  Group.IsFinitelyPresented.equiv (Steinberg.coefficientEquiv
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R:=ZMod 2) (X:=A)).symm.toRingEquiv)

end FiniteAlgebraicEnvelopes.SteinbergFiniteFree

end

end OAI
