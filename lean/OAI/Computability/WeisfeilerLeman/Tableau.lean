import OAI.Computability.WeisfeilerLeman.Digits

namespace OAI

universe uP uE uS uT uG uH uF uAlphabet

namespace WLTime.CircuitEncoding

abbrev Address (r m : ℕ) := Fin r → Fin m

def ProductAllowed {r m : ℕ} (D : Fin r → Finset (Fin m)) (a : Address r m) : Prop :=
  ∀ i, a i ∈ D i

structure Schematic (r m : ℕ) (P : Type uP) (E : Type uE) (S : Type uS) (T : Type uT) where
  kind : P → Kind
  src : E → P
  dst : E → P
  port : (e : E) → Fin (kind (dst e)).dim
  domain : E → Fin r → Finset (Fin m)
  coord : (e : E) → (i : Fin r) → domain e i → Fin m
  coord_inj : ∀ e i, Function.Injective (coord e i)
  seedGate : S → P
  seedDomain : S → Fin r → Finset (Fin m)
  testGate : T → P
  testDomain : T → Fin r → Finset (Fin m)
  seed_scalar : ∀ s, kind (seedGate s) = .scalar
  test_scalar : ∀ t, kind (testGate t) = .scalar
  rank : P × Address r m → ℕ
  forward : ∀ e a (ha : ProductAllowed (domain e) a),
    rank (src e,a) < rank (dst e,fun i => coord e i ⟨a i,ha i⟩)
  test_terminal : ∀ e a, ProductAllowed (domain e) a →
    ∀ t, testGate t = src e → ¬ProductAllowed (testDomain t) a

namespace Schematic
variable {r m : ℕ} {P : Type uP} {E : Type uE} {S : Type uS} {T : Type uT} (C : Schematic r m P E S T)

abbrev Instance (_C : Schematic r m P E S T) := P × Address r m
abbrev Connection := Σ e : E, {a : Address r m // ProductAllowed (C.domain e) a}

def transmit (e : E) (a : Address r m) (h : ProductAllowed (C.domain e) a) : Address r m :=
  fun i => C.coord e i ⟨a i,h i⟩

open scoped Classical in
noncomputable def expand : Circuit C.Instance C.Connection where
  kind g := C.kind g.1
  src e := (C.src e.1,e.2.1)
  dst e := (C.dst e.1,C.transmit e.1 e.2.1 e.2.2)
  port e := C.port e.1
  rank := C.rank
  forward e := C.forward e.1 e.2.1 e.2.2
  seed g := decide (∃ s, C.seedGate s = g.1 ∧ ProductAllowed (C.seedDomain s) g.2)
  test g := decide (∃ t, C.testGate t = g.1 ∧ ProductAllowed (C.testDomain t) g.2)
  seed_scalar := by
    intro g hg
    obtain ⟨s,hs,_⟩ := of_decide_eq_true hg
    rw [← hs]
    exact C.seed_scalar s
  test_scalar := by
    intro g hg
    obtain ⟨t,ht,_⟩ := of_decide_eq_true hg
    rw [← ht]
    exact C.test_scalar t
  test_terminal := by
    intro e
    apply decide_eq_false
    rintro ⟨t,ht,ha⟩
    exact C.test_terminal e.1 e.2.1 e.2.2 t ht ha

inductive Node (P : Type uP) (E : Type uE) where
  | gate (p : P)
  | buffer (e : E)
  | dummy
  deriving DecidableEq, Fintype

inductive Edge (E : Type uE) (S : Type uS) (T : Type uT) where
  | first (e : E)
  | second (e : E)
  | third (e : E)
  | seed (s : S)
  | test (t : T)
  deriving DecidableEq, Fintype

def nodeDim : Node P E → ℕ
  | .gate p => (C.kind p).dim
  | .buffer _ => 2
  | .dummy => 1

def edgeSrc : Edge E S T → Node P E
  | .first e => .gate (C.src e)
  | .second e => .gate (C.src e)
  | .third e => .buffer e
  | .seed s => .gate (C.seedGate s)
  | .test t => .gate (C.testGate t)

def edgeDst : Edge E S T → Node P E
  | .first e => .buffer e
  | .second e => .buffer e
  | .third e => .gate (C.dst e)
  | .seed _ => .dummy
  | .test _ => .dummy

def edgeDomain : Edge E S T → Fin r → Finset (Fin m)
  | .first e => C.domain e
  | .second e => C.domain e
  | .third e => C.domain e
  | .seed s => C.seedDomain s
  | .test t => C.testDomain t

def edgeCoord : (f : Edge E S T) → (i : Fin r) → C.edgeDomain f i → Fin m
  | .first _, _ => Subtype.val
  | .second _, _ => Subtype.val
  | .third e, i => C.coord e i
  | .seed _, _ => Subtype.val
  | .test _, _ => Subtype.val

theorem edgeCoord_inj (f : Edge E S T) (i : Fin r) : Function.Injective (C.edgeCoord f i) := by
  cases f <;> first | exact Subtype.val_injective | exact C.coord_inj _ _

def sumForm (d : ℕ) : (Fin d → Bit) →ₗ[Bit] Bit where
  toFun x := ∑ i,x i
  map_add' x y := Finset.sum_add_distrib
  map_smul' a x := by simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]

def coordForm {d : ℕ} (i : Fin d) : (Fin d → Bit) →ₗ[Bit] Bit where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def srcForm : (f : Edge E S T) → (Fin (C.nodeDim (C.edgeSrc f)) → Bit) →ₗ[Bit] Bit
  | .first _ => sumForm _
  | .second _ => sumForm _
  | .third _ => sumForm _
  | .seed _ => sumForm _
  | .test _ => sumForm _

def dstForm : (f : Edge E S T) → (Fin (C.nodeDim (C.edgeDst f)) → Bit) →ₗ[Bit] Bit
  | .first _ => coordForm (0 : Fin 2)
  | .second _ => coordForm (1 : Fin 2)
  | .third e => coordForm (C.port e)
  | .seed _ => 0
  | .test _ => 0

def dstBias : Edge E S T → Bit
  | .test _ => 1
  | _ => 0

def consistency : Compression.ConsistencyData r m (Node P E) (Edge E S T) where
  dim := C.nodeDim
  src := C.edgeSrc
  dst := C.edgeDst
  domain := C.edgeDomain
  coord := C.edgeCoord
  coord_inj := C.edgeCoord_inj
  linearSrc := C.srcForm
  linearDst := C.dstForm
  biasSrc := fun _ => 0
  biasDst := dstBias

@[simp] theorem same_transmit_first (e : E) (a : Address r m)
    (h : C.consistency.Allowed (.first e) a) :
    C.consistency.transmit (.first e) a h = a := rfl
@[simp] theorem same_transmit_second (e : E) (a : Address r m)
    (h : C.consistency.Allowed (.second e) a) :
    C.consistency.transmit (.second e) a h = a := rfl
@[simp] theorem same_transmit_third (e : E) (a : Address r m)
    (h : C.consistency.Allowed (.third e) a) :
    C.consistency.transmit (.third e) a h = C.transmit e a h := rfl
@[simp] theorem same_transmit_seed (s : S) (a : Address r m)
    (h : C.consistency.Allowed (.seed s) a) :
    C.consistency.transmit (.seed s) a h = a := rfl
@[simp] theorem same_transmit_test (t : T) (a : Address r m)
    (h : C.consistency.Allowed (.test t) a) :
    C.consistency.transmit (.test t) a h = a := rfl

theorem affineSrc_first (e : E) (a : Address r m) :
    C.consistency.affineSrc (.first e) = C.expand.output (C.src e,a) := by
  funext x
  exact add_zero _

theorem affineSrc_second (e : E) (a : Address r m) :
    C.consistency.affineSrc (.second e) = C.expand.output (C.src e,a) := by
  funext x
  exact add_zero _

theorem affineSrc_seed (e : S) (a : Address r m) :
    C.consistency.affineSrc (.seed e) = C.expand.output (C.seedGate e,a) := by
  funext x
  exact add_zero _

theorem affineSrc_test (e : T) (a : Address r m) :
    C.consistency.affineSrc (.test e) = C.expand.output (C.testGate e,a) := by
  funext x
  exact add_zero _

theorem affineSrc_third (e : E) :
    C.consistency.affineSrc (.third e) = (fun z : Fin 2 → Bit => z 0 + z 1) := by
  change (fun z : Fin 2 → Bit => (∑ i : Fin 2, (z i : Bit)) + 0) =
    (fun z : Fin 2 → Bit => (z 0 : Bit) + z 1)
  funext z
  rw [add_zero,Fin.sum_univ_two]

theorem affineDst_first (e : E) :
    C.consistency.affineDst (.first e) = (fun z : Fin 2 → Bit => z 0) := by
  funext z
  exact add_zero _

theorem affineDst_second (e : E) :
    C.consistency.affineDst (.second e) = (fun z : Fin 2 → Bit => z 1) := by
  funext z
  exact add_zero _

theorem affineDst_third (e : E) :
    C.consistency.affineDst (.third e) = (fun z : Fin (C.kind (C.dst e)).dim → Bit => z (C.port e)) := by
  funext z
  exact add_zero _

theorem affineDst_seed (e : S) :
    C.consistency.affineDst (.seed e) = (fun _ : Fin 1 → Bit => (0 : Bit)) := by
  funext z
  exact add_zero _

theorem affineDst_test (e : T) :
    C.consistency.affineDst (.test e) = (fun _ : Fin 1 → Bit => (1 : Bit)) := by
  funext z
  exact zero_add _

open Compression.ConsistencyData

open scoped Classical in

noncomputable def setsOfWitness (W : C.expand.Witness) :
    (p : Node P E) → Address r m → Set (Fin (C.nodeDim p) → Bit)
  | .gate p, a => W.gate (p,a)
  | .buffer e, a => if h : ProductAllowed (C.domain e) a then W.buffer ⟨e,⟨a,h⟩⟩ else Set.univ
  | .dummy, _ => Set.univ

theorem setsOfWitness_nonempty (W : C.expand.Witness) (p : Node P E) (a : Address r m) :
    (C.setsOfWitness W p a).Nonempty := by
  classical
  cases p with
  | gate p => exact W.gate_nonempty (p,a)
  | buffer e =>
    change (if h : ProductAllowed (C.domain e) a then W.buffer ⟨e,⟨a,h⟩⟩ else Set.univ).Nonempty
    by_cases h : ProductAllowed (C.domain e) a
    · rw [dite_eq_left h]
      exact W.buffer_nonempty ⟨e,⟨a,h⟩⟩
    · rw [dite_eq_right h]
      exact Set.univ_nonempty
  | dummy => exact Set.univ_nonempty

theorem setsOfWitness_buffer (W : C.expand.Witness) (e : E) (a : Address r m)
    (ha : ProductAllowed (C.domain e) a) :
    C.setsOfWitness W (.buffer e) a = W.buffer ⟨e,⟨a,ha⟩⟩ := by
  exact dite_eq_left ha

theorem consistent_of_witness (W : C.expand.Witness) : C.consistency.ArcConsistent := by
  classical
  refine ⟨C.setsOfWitness W,C.setsOfWitness_nonempty W,?_⟩
  intro f a ha
  cases f with
  | first e =>
    rw [C.affineSrc_first e a,C.affineDst_first e,C.same_transmit_first]
    change C.expand.output (C.src e,a) '' W.gate (C.src e,a) =
      (fun z : Fin 2 → Bit => z 0) '' C.setsOfWitness W (.buffer e) a
    rw [C.setsOfWitness_buffer W e a ha]
    exact W.first ⟨e,⟨a,ha⟩⟩
  | second e =>
    rw [C.affineSrc_second e a,C.affineDst_second e,C.same_transmit_second]
    change C.expand.output (C.src e,a) '' W.gate (C.src e,a) =
      (fun z : Fin 2 → Bit => z 1) '' C.setsOfWitness W (.buffer e) a
    rw [C.setsOfWitness_buffer W e a ha]
    exact W.second ⟨e,⟨a,ha⟩⟩
  | third e =>
    rw [C.affineSrc_third e,C.affineDst_third e,C.same_transmit_third]
    change (fun z : Fin 2 → Bit => z 0 + z 1) '' C.setsOfWitness W (.buffer e) a =
      (fun z => z (C.port e)) '' W.gate (C.dst e,C.transmit e a ha)
    rw [C.setsOfWitness_buffer W e a ha]
    exact W.third ⟨e,⟨a,ha⟩⟩
  | seed s =>
    have hs : C.expand.seed (C.seedGate s,a) = true := by
      simp only [expand,decide_eq_true_eq]
      exact ⟨s,rfl,ha⟩
    rw [C.affineSrc_seed s a,C.affineDst_seed s,C.same_transmit_seed]
    change C.expand.output (C.seedGate s,a) '' W.gate (C.seedGate s,a) =
      (fun _ : Fin 1 → Bit => (0 : Bit)) '' Set.univ
    rw [const_image Set.univ_nonempty]
    exact W.seeds _ hs
  | test t =>
    have ht : C.expand.test (C.testGate t,a) = true := by
      simp only [expand,decide_eq_true_eq]
      exact ⟨t,rfl,ha⟩
    rw [C.affineSrc_test t a,C.affineDst_test t,C.same_transmit_test]
    change C.expand.output (C.testGate t,a) '' W.gate (C.testGate t,a) =
      (fun _ : Fin 1 → Bit => (1 : Bit)) '' Set.univ
    rw [const_image Set.univ_nonempty]
    exact W.tests _ ht

noncomputable def witnessOfConsistent
    (Q : (p : Node P E) → Address r m → Set (Fin (C.nodeDim p) → Bit))
    (hQ : ∀ p a, (Q p a).Nonempty)
    (hE : ∀ f a (ha : C.consistency.Allowed f a),
      C.consistency.affineSrc f '' Q (C.edgeSrc f) a =
      C.consistency.affineDst f '' Q (C.edgeDst f) (C.consistency.transmit f a ha)) :
    C.expand.Witness where
  gate g := Q (.gate g.1) g.2
  buffer e := Q (.buffer e.1) e.2.1
  gate_nonempty g := hQ (.gate g.1) g.2
  buffer_nonempty e := hQ (.buffer e.1) e.2.1
  first e := by
    have h := hE (.first e.1) e.2.1 e.2.2
    rw [C.affineSrc_first e.1 e.2.1,C.affineDst_first e.1] at h
    exact h
  second e := by
    have h := hE (.second e.1) e.2.1 e.2.2
    rw [C.affineSrc_second e.1 e.2.1,C.affineDst_second e.1] at h
    exact h
  third e := by
    have h := hE (.third e.1) e.2.1 e.2.2
    rw [C.affineSrc_third e.1,C.affineDst_third e.1] at h
    exact h
  seeds := by
    classical
    rintro ⟨p,a⟩ hs
    obtain ⟨s,hs,ha⟩ := of_decide_eq_true hs
    change C.seedGate s=p at hs
    subst p
    have h := hE (.seed s) a ha
    rw [C.affineSrc_seed s a,C.affineDst_seed s] at h
    exact h.trans ((hQ .dummy a).image_const (0 : Bit))
  tests := by
    classical
    rintro ⟨p,a⟩ ht
    obtain ⟨t,ht,ha⟩ := of_decide_eq_true ht
    change C.testGate t=p at ht
    subst p
    have h := hE (.test t) a ha
    rw [C.affineSrc_test t a,C.affineDst_test t] at h
    exact h.trans ((hQ .dummy a).image_const (1 : Bit))

theorem consistency_iff_tests_false : C.consistency.ArcConsistent ↔
    ∀ g, C.expand.test g = true → ¬C.expand.TrueAt g := by
  rw [← C.expand.witness_iff_tests_false]
  constructor
  · rintro ⟨Q,hQ,hE⟩
    exact ⟨C.witnessOfConsistent Q hQ hE⟩
  · rintro ⟨W⟩
    exact C.consistent_of_witness W

theorem dim_le_two (p : Node P E) : C.consistency.dim p ≤ 2 := by
  cases p with
  | gate p => cases h : C.kind p <;> simp [consistency,nodeDim,h,Kind.dim]
  | buffer e => exact le_refl _
  | dummy => exact Nat.one_le_of_lt (by decide : 1 < 2)

end Schematic
end WLTime.CircuitEncoding

namespace WLTime.CircuitEncoding.Circuit
variable {G : Type uG} {E : Type uE} {H : Type uH} {F : Type uF} (C : Circuit G E) (D : Circuit H F) (f : G ≃ H)

def EdgeCover : Prop := ∀ g s p,
  (∃ e,C.dst e=g ∧ C.src e=s ∧ (C.port e).val=p) ↔
  ∃ e,D.dst e=f g ∧ D.src e=f s ∧ (D.port e).val=p

theorem incoming_of_cover (hE : C.EdgeCover D f) (g : G) (R : H → ℕ → Prop) :
    (∃ e,C.dst e=g ∧ R (f (C.src e)) (C.port e).val) ↔
      ∃ e,D.dst e=f g ∧ R (D.src e) (D.port e).val := by
  constructor
  · rintro ⟨e,he,hR⟩
    obtain ⟨e',hd,hs,hp⟩ := (hE g (C.src e) (C.port e).val).mp ⟨e,he,rfl,rfl⟩
    exact ⟨e',hd,by simpa only [hs,hp] using hR⟩
  · rintro ⟨e,he,hR⟩
    obtain ⟨e',hd,hs,hp⟩ := (hE g (f.symm (D.src e)) (D.port e).val).mpr
      ⟨e,he,by simp,rfl⟩
    exact ⟨e',hd,by simpa only [hs,hp,f.apply_symm_apply] using hR⟩

theorem truth_of_cover (hE : C.EdgeCover D f)
    (hkind : ∀ g,C.kind g=D.kind (f g)) (hseed : ∀ g,C.seed g=D.seed (f g))
    (g : G) : C.TrueAt g ↔ D.TrueAt (f g) := by
  apply C.truth_iff_of_equations (fun g => D.TrueAt (f g)) _ g
  intro g
  rw [TrueAt,← hkind g,← hseed g]
  split_ifs
  · apply or_congr Iff.rfl
    simpa only [exists_prop] using (C.incoming_of_cover D f hE g (fun s _ => D.TrueAt s)).symm
  · apply forall_congr'
    intro p
    simpa only [exists_prop] using (C.incoming_of_cover D f hE g (fun s v => v=p.val ∧ D.TrueAt s)).symm

end WLTime.CircuitEncoding.Circuit

namespace WLTime.CircuitEncoding.BoxTableau
open ProductBox
open Tableau

inductive Label (Alphabet : Type uAlphabet) (d q : ℕ) where
  | left (a b c : Alphabet) (time : Fin d) (space : Fin (q+1))
  | center (a b c : Alphabet) (time : Fin d)
  | bridge (a b c : Alphabet)
  | right (a b c : Alphabet) (time : Fin d) (space : Fin (q+1))
  | out (a b c : Alphabet)
  deriving DecidableEq

abbrev Tag (d q : ℕ) := (Fin d × Fin (q+1)) ⊕ Fin d ⊕ Unit ⊕ (Fin d × Fin (q+1)) ⊕ Unit

def labelEquiv (Alphabet : Type uAlphabet) (d q : ℕ) : Label Alphabet d q ≃ Alphabet × Alphabet × Alphabet × Tag d q where
  toFun
    | .left a b c t j => (a,b,c,.inl (t,j))
    | .center a b c t => (a,b,c,.inr (.inl t))
    | .bridge a b c => (a,b,c,.inr (.inr (.inl ())))
    | .right a b c t j => (a,b,c,.inr (.inr (.inr (.inl (t,j)))))
    | .out a b c => (a,b,c,.inr (.inr (.inr (.inr ()))))
  invFun
    | (a,b,c,.inl (t,j)) => .left a b c t j
    | (a,b,c,.inr (.inl t)) => .center a b c t
    | (a,b,c,.inr (.inr (.inl _))) => .bridge a b c
    | (a,b,c,.inr (.inr (.inr (.inl (t,j))))) => .right a b c t j
    | (a,b,c,.inr (.inr (.inr (.inr _)))) => .out a b c
  left_inv e := by cases e <;> rfl
  right_inv e := by
    rcases e with ⟨a,b,c,(⟨t,j⟩ | t | u | ⟨t,j⟩ | u)⟩
    · rfl
    · rfl
    · cases u; rfl
    · rfl
    · cases u; rfl

instance {Alphabet : Type uAlphabet} [Fintype Alphabet] (d q : ℕ) : Fintype (Label Alphabet d q) :=
  Fintype.ofEquiv _ (labelEquiv Alphabet d q).symm

variable {Alphabet : Type uAlphabet} {d q m : ℕ}
variable (F : Alphabet → Alphabet → Alphabet → Alphabet)

def src : Label Alphabet d q → Gate Alphabet
  | .left a _ _ _ _ => .scalar a
  | .center _ b _ _ => .scalar b
  | .bridge a b c => .first a b c
  | .right _ _ c _ _ => .scalar c
  | .out a b c => .second a b c

def dst : Label Alphabet d q → Gate Alphabet
  | .left a b c _ _ => .first a b c
  | .center a b c _ => .first a b c
  | .bridge a b c => .second a b c
  | .right a b c _ _ => .second a b c
  | .out a b c => .scalar (F a b c)

def port : (e : Label Alphabet d q) → Fin (dst F e).kind.dim
  | .left _ _ _ _ _ => (0 : Fin 2)
  | .center _ _ _ _ => (1 : Fin 2)
  | .bridge _ _ _ => (0 : Fin 2)
  | .right _ _ _ _ _ => (1 : Fin 2)
  | .out _ _ _ => (0 : Fin 1)

def box : Label Alphabet d q → ProductBox.Box (d+q) m
  | .left _ _ _ p s => (ProductBox.Box.carry p.castSucc).product (ProductBox.Box.carry s)
  | .center _ _ _ p => (ProductBox.Box.carry p.castSucc).product (ProductBox.Box.identity q m)
  | .bridge _ _ _ => ProductBox.Box.identity (d+q) m
  | .right _ _ _ p s => (ProductBox.Box.carry p.castSucc).product (ProductBox.Box.carry s).reverse
  | .out _ _ _ => ProductBox.Box.identity (d+q) m

def Numerical (e : Label Alphabet d q) (a b : ProductBox.Address (d+q) m) : Prop :=
  let t := Digits.value (ProductBox.time a)
  let t' := Digits.value (ProductBox.time b)
  let j := Digits.encode (ProductBox.space a)
  let j' := Digits.encode (ProductBox.space b)
  match e with
  | .left _ _ _ _ _ => t'=t+1 ∧ j'=Digits.inc (m^q) j
  | .center _ _ _ _ => t'=t+1 ∧ j'=j
  | .bridge _ _ _ => a=b
  | .right _ _ _ _ _ => t'=t+1 ∧ j'=(Digits.inc (m^q)).symm j
  | .out _ _ _ => a=b

theorem box_numerical (e : Label Alphabet d q) {a b : ProductBox.Address (d+q) m}
    (h : (box e).Rel a b) : Numerical e a b := by
  cases e with
  | left x y z p s =>
    obtain ⟨ht,hj⟩ := (ProductBox.Box.product_relation _ _ _ _).mp h
    exact ⟨(Digits.nonwrap_relation _ _).mp ⟨p,ht⟩,
      (ProductBox.Box.carry_rel _ _).mp ⟨s,hj⟩⟩
  | center x y z p =>
    obtain ⟨ht,hj⟩ := (ProductBox.Box.product_relation _ _ _ _).mp h
    exact ⟨(Digits.nonwrap_relation _ _).mp ⟨p,ht⟩,
      congrArg Digits.encode ((ProductBox.Box.identity_rel _ _).mp hj).symm⟩
  | bridge => exact (ProductBox.Box.identity_rel _ _).mp h
  | right x y z p s =>
    obtain ⟨ht,hj⟩ := (ProductBox.Box.product_relation _ _ _ _).mp h
    exact ⟨(Digits.nonwrap_relation _ _).mp ⟨p,ht⟩,
      (ProductBox.Box.borrow_rel _ _).mp ⟨s,hj⟩⟩
  | out => exact (ProductBox.Box.identity_rel _ _).mp h

def nodeMap (g : Gate Alphabet × ProductBox.Address (d+q) m) :
    Tableau.Node Alphabet (Fin (m^q)) (m^d) :=
  (g.1,Digits.encode (ProductBox.time g.2),Digits.encode (ProductBox.space g.2))

def nodeEquiv : (Gate Alphabet × ProductBox.Address (d+q) m) ≃
    Tableau.Node Alphabet (Fin (m^q)) (m^d) :=
  Equiv.prodCongr (Equiv.refl _) ProductBox.addressEquiv

@[simp] theorem nodeEquiv_apply (g : Gate Alphabet × ProductBox.Address (d+q) m) :
    nodeEquiv g=nodeMap g := rfl

theorem numerical_forward (e : Label Alphabet d q) {a b : ProductBox.Address (d+q) m}
    (h : Numerical e a b) :
    Tableau.rank (nodeMap (src e,a)) < Tableau.rank (nodeMap (dst F e,b)) := by
  cases e <;> simp only [Numerical] at h
  all_goals simp only [Tableau.rank,nodeMap,src,dst,Gate.phase,Digits.value] at *
  all_goals first | omega | subst b; omega

theorem box_forward (e : Label Alphabet d q) (a : ProductBox.Address (d+q) m)
    (ha : (box e).Allowed a) :
    Tableau.rank (nodeMap (src e,a)) <
      Tableau.rank (nodeMap (dst F e,(box e).apply a)) :=
  numerical_forward F e (box_numerical e ⟨ha,rfl⟩)

theorem left_covered (x y z : Alphabet) (a b : ProductBox.Address (d+q) m)
    (ht : Digits.value (ProductBox.time b)=Digits.value (ProductBox.time a)+1)
    (hj : Digits.encode (ProductBox.space b)=Digits.inc (m^q) (Digits.encode (ProductBox.space a))) :
    ∃ p s,(box (.left x y z p s)).Rel a b := by
  obtain ⟨p,hp⟩ := (Digits.nonwrap_relation _ _).mpr ht
  obtain ⟨s,hs⟩ := (ProductBox.Box.carry_rel _ _).mpr hj
  exact ⟨p,s,(ProductBox.Box.product_relation _ _ _ _).mpr ⟨hp,hs⟩⟩

theorem center_covered (x y z : Alphabet) (a b : ProductBox.Address (d+q) m)
    (ht : Digits.value (ProductBox.time b)=Digits.value (ProductBox.time a)+1)
    (hj : Digits.encode (ProductBox.space b)=Digits.encode (ProductBox.space a)) :
    ∃ p,(box (.center x y z p)).Rel a b := by
  obtain ⟨p,hp⟩ := (Digits.nonwrap_relation _ _).mpr ht
  exact ⟨p,(ProductBox.Box.product_relation _ _ _ _).mpr
    ⟨hp,(ProductBox.Box.identity_rel _ _).mpr (Digits.encode.injective hj.symm)⟩⟩

theorem right_covered (x y z : Alphabet) (a b : ProductBox.Address (d+q) m)
    (ht : Digits.value (ProductBox.time b)=Digits.value (ProductBox.time a)+1)
    (hj : Digits.encode (ProductBox.space b)=(Digits.inc (m^q)).symm (Digits.encode (ProductBox.space a))) :
    ∃ p s,(box (.right x y z p s)).Rel a b := by
  obtain ⟨p,hp⟩ := (Digits.nonwrap_relation _ _).mpr ht
  obtain ⟨s,hs⟩ := (ProductBox.Box.borrow_rel _ _).mpr hj
  exact ⟨p,s,(ProductBox.Box.product_relation _ _ _ _).mpr ⟨hp,hs⟩⟩

theorem realizes (e : Label Alphabet d q) (a b : ProductBox.Address (d+q) m)
    (hab : (box e).Rel a b) :
    ∃ u : Tableau.Connection Alphabet (Fin (m^q)) (m^d),
      Tableau.source (Digits.inc (m^q)) u=nodeMap (src e,a) ∧
      Tableau.target F u=nodeMap (dst F e,b) ∧
      (Tableau.port F u).val=(port F e).val := by
  have hn := box_numerical e hab
  have prev_eq (h : Digits.value (ProductBox.time b)=Digits.value (ProductBox.time a)+1) :
      ∃ hb : 0<(Digits.encode (ProductBox.time b)).val,
        Tableau.prevTime (Digits.encode (ProductBox.time b)) hb=Digits.encode (ProductBox.time a) := by
    have hb : 0<(Digits.encode (ProductBox.time b)).val := by change 0<Digits.value _; omega
    exact ⟨hb,Fin.ext (by change Digits.value (ProductBox.time b)-1=Digits.value (ProductBox.time a); omega)⟩
  cases e with
  | left x y z p j =>
    obtain ⟨ht,hj⟩ := hn
    obtain ⟨hb,hprev⟩ := prev_eq ht
    refine ⟨.left x y z (Digits.encode (ProductBox.time b)) hb (Digits.encode (ProductBox.space b)),?_,rfl,rfl⟩
    simp only [Tableau.source,src,nodeMap,hprev,hj,Equiv.symm_apply_apply]
  | center x y z p =>
    obtain ⟨ht,hj⟩ := hn
    obtain ⟨hb,hprev⟩ := prev_eq ht
    refine ⟨.center x y z (Digits.encode (ProductBox.time b)) hb (Digits.encode (ProductBox.space b)),?_,rfl,rfl⟩
    simp only [Tableau.source,src,nodeMap,hprev,hj]
  | bridge x y z =>
    change a=b at hn
    subst b
    exact ⟨.bridge x y z (Digits.encode (ProductBox.time a)) (Digits.encode (ProductBox.space a)),rfl,rfl,rfl⟩
  | right x y z p j =>
    obtain ⟨ht,hj⟩ := hn
    obtain ⟨hb,hprev⟩ := prev_eq ht
    refine ⟨.right x y z (Digits.encode (ProductBox.time b)) hb (Digits.encode (ProductBox.space b)),?_,rfl,rfl⟩
    simp only [Tableau.source,src,nodeMap,hprev,hj,Equiv.apply_symm_apply]
  | out x y z =>
    change a=b at hn
    subst b
    exact ⟨.out x y z (Digits.encode (ProductBox.time a)) (Digits.encode (ProductBox.space a)),rfl,rfl,rfl⟩

theorem covers (u : Tableau.Connection Alphabet (Fin (m^q)) (m^d)) :
    ∃ e : Label Alphabet d q,
      src e=(Tableau.source (Digits.inc (m^q)) u).1 ∧
      dst F e=(Tableau.target F u).1 ∧
      (box e).Rel (ProductBox.addressEquiv.symm (Tableau.source (Digits.inc (m^q)) u).2)
        (ProductBox.addressEquiv.symm (Tableau.target F u).2) ∧
      (port F e).val=(Tableau.port F u).val := by
  cases u with
  | left x y z t ht j =>
    obtain ⟨p,s,hp⟩ := left_covered x y z
      (ProductBox.addressEquiv.symm (Tableau.prevTime t ht,(Digits.inc (m^q)).symm j))
      (ProductBox.addressEquiv.symm (t,j)) (by
        simp only [ProductBox.addressEquiv,Equiv.coe_fn_symm_mk,ProductBox.time_append,
          Digits.value,Equiv.apply_symm_apply,Tableau.prevTime]
        omega) (by
        simp only [ProductBox.addressEquiv,Equiv.coe_fn_symm_mk,ProductBox.space_append,
          Equiv.apply_symm_apply])
    exact ⟨.left x y z p s,rfl,rfl,hp,rfl⟩
  | center x y z t ht j =>
    obtain ⟨p,hp⟩ := center_covered x y z
      (ProductBox.addressEquiv.symm (Tableau.prevTime t ht,j))
      (ProductBox.addressEquiv.symm (t,j)) (by
        simp only [ProductBox.addressEquiv,Equiv.coe_fn_symm_mk,ProductBox.time_append,
          Digits.value,Equiv.apply_symm_apply,Tableau.prevTime]
        omega) (by
        simp only [ProductBox.addressEquiv,Equiv.coe_fn_symm_mk,ProductBox.space_append,
          Equiv.apply_symm_apply])
    exact ⟨.center x y z p,rfl,rfl,hp,rfl⟩
  | bridge x y z t j =>
    exact ⟨.bridge x y z,rfl,rfl,(ProductBox.Box.identity_rel _ _).mpr rfl,rfl⟩
  | right x y z t ht j =>
    obtain ⟨p,s,hp⟩ := right_covered x y z
      (ProductBox.addressEquiv.symm (Tableau.prevTime t ht,Digits.inc (m^q) j))
      (ProductBox.addressEquiv.symm (t,j)) (by
        simp only [ProductBox.addressEquiv,Equiv.coe_fn_symm_mk,ProductBox.time_append,
          Digits.value,Equiv.apply_symm_apply,Tableau.prevTime]
        omega) (by
        simp only [ProductBox.addressEquiv,Equiv.coe_fn_symm_mk,ProductBox.space_append,
          Equiv.apply_symm_apply,Equiv.symm_apply_apply])
    exact ⟨.right x y z p s,rfl,rfl,hp,rfl⟩
  | out x y z t j =>
    exact ⟨.out x y z,rfl,rfl,(ProductBox.Box.identity_rel _ _).mpr rfl,rfl⟩

section Initialization
open scoped Classical
variable (input : Fin m → Alphabet) (blank : Alphabet)

noncomputable def initialDigit (a : ProductBox.Address (q+1) m) : Alphabet :=
  if ∀ i : Fin q,(a i.succ).val=0 then input (a 0) else blank

noncomputable def initialRing (j : Fin (m^(q+1))) : Alphabet :=
  initialDigit input blank (Digits.encode.symm j)

def seedGate : Alphabet ⊕ Fin q → Gate Alphabet
  | .inl f => .scalar f
  | .inr _ => .scalar blank

noncomputable def positionDomain : Alphabet ⊕ Fin q → Fin (q+1) → Finset (Fin m)
  | .inl f => Fin.cases (Finset.univ.filter fun x => input x=f)
      (fun _ => Finset.univ.filter fun x => x.val=0)
  | .inr i => fun j => Finset.univ.filter fun x => j=i.succ → x.val≠0

noncomputable def seedDomain (s : Alphabet ⊕ Fin q) : Fin (d+(q+1)) → Finset (Fin m) :=
  Fin.addCases (fun _ => Finset.univ.filter fun x => x.val=0) (positionDomain input s)

theorem seed_allowed (s : Alphabet ⊕ Fin q) (a : ProductBox.Address (d+(q+1)) m) :
    ProductAllowed (seedDomain input s) a ↔
      (∀ i,(ProductBox.time a i).val=0) ∧
      ProductAllowed (positionDomain input s) (ProductBox.space a) := by
  simp only [ProductAllowed,seedDomain,Fin.forall_fin_add,Fin.addCases_left,
    Fin.addCases_right,Finset.mem_filter,Finset.mem_univ,true_and]

theorem input_allowed (f : Alphabet) (a : ProductBox.Address (q+1) m) :
    ProductAllowed (positionDomain input (.inl f)) a ↔
      input (a 0)=f ∧ ∀ i : Fin q,(a i.succ).val=0 := by
  simp only [ProductAllowed,positionDomain,Fin.forall_fin_succ,Fin.cases_zero,
    Fin.cases_succ,Finset.mem_filter,Finset.mem_univ,true_and]

theorem blank_allowed (i : Fin q) (a : ProductBox.Address (q+1) m) :
    ProductAllowed (positionDomain input (.inr i)) a ↔ (a i.succ).val≠0 := by
  simp only [ProductAllowed,positionDomain,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h; exact h i.succ rfl
  · intro h j hj; simpa only [hj] using h

theorem seed_spec (hm : 0< m) (f : Alphabet) (a : ProductBox.Address (d+(q+1)) m) :
    (∃ s,seedGate blank s=.scalar f ∧ ProductAllowed (seedDomain input s) a) ↔
      Digits.value (ProductBox.time a)=0 ∧ f=initialDigit input blank (ProductBox.space a) := by
  constructor
  · rintro ⟨s,hs,ha⟩
    obtain ⟨ht,hp⟩ := (seed_allowed input s a).mp ha
    refine ⟨(Digits.value_eq_zero_iff hm _).mpr ht,?_⟩
    cases s with
    | inl x =>
      have hx : x=f := Gate.scalar.inj hs
      obtain ⟨hi,hh⟩ := (input_allowed input x _).mp hp
      simp only [initialDigit,ite_eq_left hh,← hx,hi]
    | inr i =>
      have hf : blank=f := Gate.scalar.inj hs
      have hi := (blank_allowed input i _).mp hp
      have hh : ¬∀ j : Fin q,(ProductBox.space a j.succ).val=0 := fun h => hi (h i)
      simp only [initialDigit,ite_eq_right hh,← hf]
  · rintro ⟨ht,hf⟩
    have ht' := (Digits.value_eq_zero_iff hm _).mp ht
    by_cases hh : ∀ j : Fin q,(ProductBox.space a j.succ).val=0
    · refine ⟨.inl f,rfl,(seed_allowed input _ _).mpr ⟨ht',?_⟩⟩
      apply (input_allowed input _ _).mpr
      exact ⟨by simpa only [initialDigit,ite_eq_left hh] using hf.symm,hh⟩
    · obtain ⟨i,hi⟩ := not_forall.mp hh
      refine ⟨.inr i,?_,(seed_allowed input _ _).mpr ⟨ht',?_⟩⟩
      · change Gate.scalar blank=.scalar f
        simpa only [initialDigit,ite_eq_right hh] using congrArg Gate.scalar hf.symm
      · exact (blank_allowed input i _).mpr hi

variable (accepting : Alphabet → Prop)

def testGate (f : {f : Alphabet // accepting f}) : Gate Alphabet := .scalar f.val

noncomputable def testDomain (_f : {f : Alphabet // accepting f}) :
    Fin (d+(q+1)) → Finset (Fin m) :=
  Fin.addCases (fun _ => Finset.univ.filter fun x => x.val+1=m) (fun _ => Finset.univ)

theorem test_allowed (f : {f : Alphabet // accepting f}) (a : ProductBox.Address (d+(q+1)) m) :
    ProductAllowed (testDomain accepting f) a ↔ Digits.value (ProductBox.time a)+1=m^d := by
  rw [Digits.value_last_iff]
  simp only [ProductAllowed,testDomain,Fin.forall_fin_add,Fin.addCases_left,
    Fin.addCases_right,Finset.mem_filter,Finset.mem_univ,true_and,and_true,forall_const]

theorem test_spec (f : Alphabet) (a : ProductBox.Address (d+(q+1)) m) :
    (∃ s,testGate accepting s=.scalar f ∧ ProductAllowed (testDomain accepting s) a) ↔
      Digits.value (ProductBox.time a)+1=m^d ∧ accepting f := by
  simp only [testGate,Gate.scalar.injEq,test_allowed accepting]
  constructor
  · rintro ⟨s,hs,ht⟩; exact ⟨ht,hs ▸ s.property⟩
  · rintro ⟨ht,hf⟩; exact ⟨⟨f,hf⟩,rfl,ht⟩

theorem terminal (e : Label Alphabet d (q+1)) (a : ProductBox.Address (d+(q+1)) m)
    (ha : (box e).Allowed a) (f : {f : Alphabet // accepting f})
    (he : testGate accepting f=src e) : ¬ProductAllowed (testDomain accepting f) a := by
  intro ht
  have ht' := (test_allowed accepting f a).mp ht
  have hn := box_numerical e ⟨ha,rfl⟩
  have hl := (Digits.encode (ProductBox.time ((box e).apply a))).isLt
  cases e <;> simp only [testGate,src,Gate.scalar.injEq,reduceCtorEq] at he
  all_goals simp only [Numerical] at hn
  all_goals change Digits.value (ProductBox.time ((box _).apply a))< m^d at hl
  all_goals omega

noncomputable def schematic : Schematic (d+(q+1)) m (Gate Alphabet)
    (Label Alphabet d (q+1)) (Alphabet ⊕ Fin q) {f : Alphabet // accepting f} where
  kind := Gate.kind
  src := src
  dst := dst F
  port := port F
  domain e := (box e).domain
  coord e i x := (box e).coord i x.val
  coord_inj e i := (box e).coord i |>.injective.comp Subtype.val_injective
  seedGate := seedGate blank
  seedDomain := seedDomain input
  testGate := testGate accepting
  testDomain := testDomain accepting
  seed_scalar s := by cases s <;> rfl
  test_scalar _ := rfl
  rank g := Tableau.rank (nodeMap g)
  forward e a ha := box_forward F e a ha
  test_terminal := terminal accepting

theorem edge_cover :
    (schematic F input blank accepting : Schematic (d+(q+1)) m _ _ _ _).expand.EdgeCover
      (Tableau.circuit F (Digits.inc (m^(q+1))) (initialRing input blank) accepting) nodeEquiv := by
  intro g s p
  constructor
  · rintro ⟨⟨e,a,ha⟩,hg,hs,hp⟩
    obtain ⟨u,hu,hv,hw⟩ := realizes F e a ((box e).apply a) ⟨ha,rfl⟩
    refine ⟨u,?_,?_,hw.trans hp⟩
    · exact hv.trans (congrArg nodeEquiv hg)
    · exact hu.trans (congrArg nodeEquiv hs)
  · rintro ⟨u,hg,hs,hp⟩
    change Tableau.target F u=nodeEquiv g at hg
    change Tableau.source (Digits.inc (m^(q+1))) u=nodeEquiv s at hs
    obtain ⟨e,he,hf,hab,hp'⟩ := covers F u
    let a := ProductBox.addressEquiv.symm (Tableau.source (Digits.inc (m^(q+1))) u).2
    let b := ProductBox.addressEquiv.symm (Tableau.target F u).2
    have hsrc : (src e,a)=nodeEquiv.symm (Tableau.source (Digits.inc (m^(q+1))) u) := by
      exact Prod.ext he rfl
    have hdst : (dst F e,(box e).apply a)=nodeEquiv.symm (Tableau.target F u) := by
      exact Prod.ext hf hab.2
    refine ⟨⟨e,a,hab.1⟩,?_,?_,hp'.trans hp⟩
    · change (dst F e,(box e).apply a)=g
      rw [hdst,hg,Equiv.symm_apply_apply]
    · change (src e,a)=s
      rw [hsrc,hs,Equiv.symm_apply_apply]

 theorem seed_eq (hm : 0< m) (g : Gate Alphabet × ProductBox.Address (d+(q+1)) m) :
    (schematic F input blank accepting).expand.seed g =
      (Tableau.circuit F (Digits.inc (m^(q+1))) (initialRing input blank) accepting).seed (nodeEquiv g) := by
  classical
  rcases g with ⟨g,a⟩
  cases g with
  | scalar f =>
    change decide (∃ s,seedGate blank s=.scalar f ∧ ProductAllowed (seedDomain input s) a) =
      decide (Digits.value (ProductBox.time a)=0 ∧ f=initialRing input blank (Digits.encode (ProductBox.space a)))
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq,seed_spec input blank hm,initialRing,Equiv.symm_apply_apply]
  | first x y z =>
    change decide (∃ s,seedGate blank s=.first x y z ∧ ProductAllowed (seedDomain input s) a)=false
    apply decide_eq_false
    rintro ⟨s,hs,_⟩
    cases s <;> cases hs
  | second x y z =>
    change decide (∃ s,seedGate blank s=.second x y z ∧ ProductAllowed (seedDomain input s) a)=false
    apply decide_eq_false
    rintro ⟨s,hs,_⟩
    cases s <;> cases hs

theorem test_eq (g : Gate Alphabet × ProductBox.Address (d+(q+1)) m) :
    (schematic F input blank accepting).expand.test g =
      (Tableau.circuit F (Digits.inc (m^(q+1))) (initialRing input blank) accepting).test (nodeEquiv g) := by
  classical
  rcases g with ⟨g,a⟩
  cases g with
  | scalar f =>
    change decide (∃ s,testGate accepting s=.scalar f ∧ ProductAllowed (testDomain accepting s) a) =
      decide (Digits.value (ProductBox.time a)+1=m^d ∧ accepting f)
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq,test_spec accepting]
  | first x y z =>
    change decide (∃ s,Gate.scalar s.val=.first x y z ∧ ProductAllowed (testDomain accepting s) a)=false
    simp
  | second x y z =>
    change decide (∃ s,Gate.scalar s.val=.second x y z ∧ ProductAllowed (testDomain accepting s) a)=false
    simp

theorem truth_eq (hm : 0< m) (g : Gate Alphabet × ProductBox.Address (d+(q+1)) m) :
    (schematic F input blank accepting).expand.TrueAt g ↔
      (Tableau.circuit F (Digits.inc (m^(q+1))) (initialRing input blank) accepting).TrueAt (nodeEquiv g) :=
  Circuit.truth_of_cover _ _ nodeEquiv (edge_cover F input blank accepting)
    (fun _ => rfl) (seed_eq F input blank accepting hm) g

theorem local_equivalence (hm : 0< m) :
    (∀ g, (schematic F input blank accepting : Schematic (d+(q+1)) m _ _ _ _).expand.test g=true →
      ¬(schematic F input blank accepting).expand.TrueAt g) ↔
      ∀ j, ¬accepting (Tableau.run F (Digits.inc (m^(q+1))) (initialRing input blank) (m^d-1) j) := by
  rw [← Tableau.tests_false_iff F (Digits.inc (m^(q+1))) (initialRing input blank) (Nat.pow_pos hm) accepting]
  constructor
  · intro h g
    have hi := h (nodeEquiv.symm g)
    simpa only [test_eq F input blank accepting,truth_eq F input blank accepting hm,
      Equiv.apply_symm_apply] using hi
  · intro h g
    simpa only [test_eq F input blank accepting,truth_eq F input blank accepting hm] using h (nodeEquiv g)

end Initialization

end WLTime.CircuitEncoding.BoxTableau

end OAI
