import OAI.Computability.WLIdentification.AddressArithmetic

namespace OAI

namespace WLIdentification

namespace CellularCircuit
open BinaryAddress
variable {d : ℕ} {A Z : Type}

abbrev Address (d : ℕ) := Bits (d + d)
def time (x : Address d) : Bits d := fun i => x (Fin.castAdd d i)
def position (x : Address d) : Bits d := fun i => x (Fin.natAdd d i)
def address (t j : Bits d) : Address d := Fin.append t j

@[simp] theorem time_address (t j : Bits d) : time (address t j) = t := by funext i; exact Fin.append_left t j i
@[simp] theorem position_address (t j : Bits d) : position (address t j) = j := by funext i; exact Fin.append_right t j i
@[simp] theorem address_parts (x : Address d) : address (time x) (position x) = x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact Fin.append_left (time x) (position x) j
  · exact Fin.append_right (time x) (position x) j

theorem concat_address (D E : ProductMap d) (t j u v : Bits d) :
    (D.concat E).Rel (address t j) (address u v) ↔ D.Rel t u ∧ E.Rel j v := by
  rw [ProductMap.concat_rel]
  simp only [address, Fin.append_left, Fin.append_right]

inductive Gate (A : Type) where
  | scalar (f : A)
  | first (a b c : A)
  | second (a b c : A)
  deriving Fintype, DecidableEq

abbrev dimension : Gate A → ℕ
  | .scalar _ => 1
  | .first _ _ _ => 2
  | .second _ _ _ => 2

inductive Connection (d : ℕ) (A : Type) where
  | left (a b c : A) (h : Fin d) (j : Option (Fin d))
  | center (a b c : A) (h : Fin d)
  | right (a b c : A) (h : Fin d) (j : Option (Fin d))
  | join (a b c : A)
  | output (a b c : A)
  deriving DecidableEq

abbrev ConnectionCode (d : ℕ) (A : Type) :=
  (A × A × A) × ((Fin d × Option (Fin d)) ⊕
    (Fin d ⊕ ((Fin d × Option (Fin d)) ⊕ (Unit ⊕ Unit))))

def Connection.encode : Connection d A → ConnectionCode d A
  | .left a b c h j => ((a, b, c), .inl (h, j))
  | .center a b c h => ((a, b, c), .inr (.inl h))
  | .right a b c h j => ((a, b, c), .inr (.inr (.inl (h, j))))
  | .join a b c => ((a, b, c), .inr (.inr (.inr (.inl ()))))
  | .output a b c => ((a, b, c), .inr (.inr (.inr (.inr ()))))

def Connection.decode : ConnectionCode d A → Connection d A
  | ((a, b, c), .inl (h, j)) => .left a b c h j
  | ((a, b, c), .inr (.inl h)) => .center a b c h
  | ((a, b, c), .inr (.inr (.inl (h, j)))) => .right a b c h j
  | ((a, b, c), .inr (.inr (.inr (.inl _)))) => .join a b c
  | ((a, b, c), .inr (.inr (.inr (.inr _)))) => .output a b c

def Connection.equiv : Connection d A ≃ ConnectionCode d A where
  toFun := Connection.encode
  invFun := Connection.decode
  left_inv e := by cases e <;> rfl
  right_inv e := by
    rcases e with ⟨⟨a, b, c⟩, e⟩
    rcases e with ⟨h, j⟩ | e
    · rfl
    rcases e with h | e
    · rfl
    rcases e with ⟨h, j⟩ | e
    · rfl
    rcases e with u | u <;> cases u <;> rfl

instance [Fintype A] : Fintype (Connection d A) := Fintype.ofEquiv _ Connection.equiv.symm

@[simp] theorem card_connection [Fintype A] : Fintype.card (Connection d A) =
    Fintype.card A ^ 3 * (2 * d ^ 2 + 3 * d + 2) := by
  rw [Fintype.card_congr Connection.equiv]
  simp only [ConnectionCode, Fintype.card_prod, Fintype.card_sum, Fintype.card_option,
    Fintype.card_fin, Fintype.card_unit]
  ring

abbrev source : Connection d A → Gate A
  | .left a _ _ _ _ => .scalar a
  | .center _ b _ _ => .scalar b
  | .right _ _ c _ _ => .scalar c
  | .join a b c => .first a b c
  | .output a b c => .second a b c

abbrev target (F : A → A → A → A) : Connection d A → Gate A
  | .left a b c _ _ => .first a b c
  | .center a b c _ => .first a b c
  | .right a b c _ _ => .second a b c
  | .join a b c => .second a b c
  | .output a b c => .scalar (F a b c)

abbrev port (F : A → A → A → A) (e : Connection d A) : Fin (dimension (target F e)) :=
  match e with
  | .left _ _ _ _ _ => 0
  | .center _ _ _ _ => 1
  | .right _ _ _ _ _ => 1
  | .join _ _ _ => 0
  | .output _ _ _ => 0

def edgeMap : Connection d A → ProductMap (d + d)
  | .left _ _ _ h j => (carryMap h).concat (cycleMap d j)
  | .center _ _ _ h => (carryMap h).concat (ProductMap.identity d)
  | .right _ _ _ h j => (carryMap h).concat (cycleMap d j).inverse
  | .join _ _ _ => ProductMap.identity _
  | .output _ _ _ => ProductMap.identity _

variable (F : A → A → A → A) (seedLetter : Z → A) (seedDomain : Z → ProductMap d)
    (accept : A → Prop)

variable [Fintype A] [Fintype Z]

noncomputable def gateIndexValue : Gate A → ℕ
  | .scalar a => Nat.pair 0 (NaturalCode.fixed A a)
  | .first a b c => Nat.pair 1 (Nat.pair (NaturalCode.fixed A a) (Nat.pair (NaturalCode.fixed A b) (NaturalCode.fixed A c)))
  | .second a b c => Nat.pair 2 (Nat.pair (NaturalCode.fixed A a) (Nat.pair (NaturalCode.fixed A b) (NaturalCode.fixed A c)))

noncomputable def gateIndex : Gate A ↪ ℕ where
  toFun := gateIndexValue
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp only [gateIndexValue, Nat.pair_eq_pair, Nat.reduceEqDiff, false_and,
        true_and, (NaturalCode.fixed A).injective.eq_iff] at h
    all_goals simp_all

noncomputable def connectionIndex : Connection d A ↪ ℕ :=
  Connection.equiv.toEmbedding.trans (NaturalCode.prod
    (NaturalCode.prod (NaturalCode.fixed A) (NaturalCode.prod (NaturalCode.fixed A) (NaturalCode.fixed A)))
    (NaturalCode.sum (NaturalCode.prod (NaturalCode.fin d) (NaturalCode.option (NaturalCode.fin d)))
      (NaturalCode.sum (NaturalCode.fin d)
        (NaturalCode.sum (NaturalCode.prod (NaturalCode.fin d) (NaturalCode.option (NaturalCode.fin d)))
          (NaturalCode.sum NaturalCode.unit NaturalCode.unit)))))

noncomputable abbrev circuit : ProductCircuit (d + d) (Gate A) (Connection d A) Z {f : A // accept f} where
  pointIndex := gateIndex
  edgeIndex := connectionIndex
  seedIndex := NaturalCode.fixed Z
  testIndex := NaturalCode.subtype (NaturalCode.fixed A) _
  dimension := dimension
  dimension_bound p := by cases p <;> simp
  source := source
  target := target F
  port := port F
  edgeMap := edgeMap
  seedType z := .scalar (seedLetter z)
  seed_scalar _ := rfl
  seedMap z := (ProductMap.singleton (fun _ => false) (fun _ => false)).concat (seedDomain z)
  testType f := .scalar f.val
  test_scalar _ := rfl
  testMap _ := (ProductMap.singleton (fun _ => true) (fun _ => true)).concat (ProductMap.identity d)

/-- A genuine synchronous radius-one automaton on the cyclic address alphabet. -/
noncomputable def evolution (init : Bits d → A) : ℕ → Bits d → A
  | 0 => init
  | t + 1 => fun j => F (evolution init t ((rotation d).symm j))
      (evolution init t j) (evolution init t (rotation d j))

variable (init : Bits d → A)

/-- The intended input-port semantics; only scalar gates can be seeds. -/
noncomputable def SemPort : (p : Gate A) → Address d → Fin (dimension p) → Prop
  | .scalar f, x, _ => f = evolution F init (value (time x)) (position x)
  | .first a b _, x, i => 0 < value (time x) ∧
      if i = 0 then a = evolution F init (value (time x) - 1) ((rotation d).symm (position x))
      else b = evolution F init (value (time x) - 1) (position x)
  | .second a b c, x, i => 0 < value (time x) ∧
      if i = 0 then
        a = evolution F init (value (time x) - 1) ((rotation d).symm (position x)) ∧
        b = evolution F init (value (time x) - 1) (position x)
      else c = evolution F init (value (time x) - 1) (rotation d (position x))

variable {F init}

omit [Fintype A] in
theorem edge_sound (e : Connection d A) {x y : Address d} (h : (edgeMap e).Rel x y)
    (hx : ∀ i, SemPort F init (source e) x i) : SemPort F init (target F e) y (port F e) := by
  cases e with
  | left a b c hct hcp =>
    obtain ⟨ht, hp⟩ := (ProductMap.concat_rel _ _ _ _).mp h
    have htime : value (time y) = value (time x) + 1 := carryMap_sound hct ht
    have hpos : position y = rotation d (position x) :=
      (cycleMap_sound hcp hp).trans (rotation_advance _).symm
    simpa [SemPort, htime, hpos] using hx 0
  | center a b c hct =>
    obtain ⟨ht, hp⟩ := (ProductMap.concat_rel _ _ _ _).mp h
    have htime : value (time y) = value (time x) + 1 := carryMap_sound hct ht
    have hpos : position x = position y := (ProductMap.identity_rel _ _).mp hp
    simpa [SemPort, htime, hpos] using hx 0
  | right a b c hct hcp =>
    obtain ⟨ht, hp⟩ := (ProductMap.concat_rel _ _ _ _).mp h
    have htime : value (time y) = value (time x) + 1 := carryMap_sound hct ht
    have hpos : position x = rotation d (position y) :=
      (cycleMap_sound hcp ((ProductMap.inverse_rel _ _ _).mp hp)).trans (rotation_advance _).symm
    simpa [SemPort, htime, hpos] using hx 0
  | join a b c =>
    obtain rfl := (ProductMap.identity_rel _ _).mp h
    have h0 := hx 0
    have h1 := hx 1
    simp only [SemPort, ↓reduceIte, show (1 : Fin 2) ≠ 0 from by decide] at h0 h1 ⊢
    exact ⟨h0.1, h0.2, h1.2⟩
  | output a b c =>
    obtain rfl := (ProductMap.identity_rel _ _).mp h
    have h0 := hx 0
    have h1 := hx 1
    simp only [SemPort, ↓reduceIte, show (1 : Fin 2) ≠ 0 from by decide] at h0 h1 ⊢
    have ht : value (time x) = (value (time x) - 1) + 1 := by omega
    conv_rhs => rw [ht]
    dsimp only [evolution]
    rw [h0.2.1, h0.2.2, h1.2]

variable (F init)

/-- Exact compressed initialization, to be instantiated by singletons plus
at most d+1 threshold domains below. -/
def SeedCorrect : Prop := ∀ f x,
  (∃ z y, seedLetter z = f ∧ (seedDomain z).Rel x y) ↔ f = init x

variable (hseed : SeedCorrect seedLetter seedDomain init)

include hseed in
theorem port_sound {p : Gate A} {x : Address d} {i : Fin (dimension p)}
    (h : (circuit F seedLetter seedDomain accept).PortTrue p x i) : SemPort F init p x i := by
  apply ProductCircuit.PortTrue.rec (motive := fun p x i _ => SemPort F init p x i) ?_ ?_ h
  · intro z a i
    have hrel := ProductMap.rel_point
      ((circuit F seedLetter seedDomain accept).seedMap z) a
    obtain ⟨ht, hp⟩ := (ProductMap.concat_rel _ _ _ _).mp hrel
    obtain ⟨ht, _⟩ := (ProductMap.singleton_rel _ _ _ _).mp ht
    have hs := (hseed (seedLetter z) _).mp ⟨z, _, rfl, hp⟩
    change time (((circuit F seedLetter seedDomain accept).seedMap z).source a) = (fun _ => false) at ht
    change seedLetter z = evolution F init (value (time (((circuit F seedLetter seedDomain accept).seedMap z).source a))) (position _)
    rw [ht, value_zero]
    exact hs
  · intro e a _ ih
    exact edge_sound e (ProductMap.rel_point (edgeMap e) a) ih

include hseed in
theorem scalar_complete (t j : Bits d) :
    (circuit F seedLetter seedDomain accept).True (.scalar (evolution F init (value t) j)) (address t j) := by
  generalize ht : value t = n
  induction n using Nat.strong_induction_on generalizing t j with
  | h n ih =>
    let C := circuit F seedLetter seedDomain accept
    by_cases hn : n = 0
    · have hzero : t = fun _ => false := value_injective d (by rw [ht, hn, value_zero])
      subst t
      obtain ⟨z, y, hz, hrel⟩ := (hseed (init j) j).mpr rfl
      have hs := C.seed_rel z ((concat_address _ _ _ _ _ _).mpr
        ⟨(ProductMap.singleton_rel _ _ _ _).mpr ⟨rfl, rfl⟩, hrel⟩ :
          (C.seedMap z).Rel (address (fun _ => false) j) (address (fun _ => false) y))
      simpa only [C, circuit, value_zero, evolution, hz, hn] using hs
    · have hnpos : 0 < n := by omega
      obtain ⟨u, hu⟩ := value_surjective d (n - 1) (by have := value_lt t; omega)
      obtain ⟨hct, htime⟩ := carryMap_complete u t (by omega)
      let a := evolution F init (n - 1) ((rotation d).symm j)
      let b := evolution F init (n - 1) j
      let c := evolution F init (n - 1) (rotation d j)
      have ha : C.True (.scalar a) (address u ((rotation d).symm j)) := by
        simpa only [hu] using ih (n - 1) (by omega) u ((rotation d).symm j) hu
      have hb : C.True (.scalar b) (address u j) := by
        simpa only [hu] using ih (n - 1) (by omega) u j hu
      have hc : C.True (.scalar c) (address u (rotation d j)) := by
        simpa only [hu] using ih (n - 1) (by omega) u (rotation d j) hu
      obtain ⟨hleft, hleftrel⟩ := cycleMap_complete ((rotation d).symm j)
      have hleftrel' : (cycleMap d hleft).Rel ((rotation d).symm j) j := by
        simpa only [← rotation_advance, Equiv.apply_symm_apply] using hleftrel
      obtain ⟨hright, hrightrel⟩ := cycleMap_complete j
      have hrightrel' : (cycleMap d hright).inverse.Rel (rotation d j) j := by
        rw [ProductMap.inverse_rel]
        simpa only [← rotation_advance] using hrightrel
      have hp0 : C.PortTrue (.first a b c) (address t j) 0 :=
        C.edge_rel (.left a b c hct hleft)
          ((concat_address _ _ _ _ _ _).mpr ⟨htime, hleftrel'⟩) ha
      have hp1 : C.PortTrue (.first a b c) (address t j) 1 :=
        C.edge_rel (.center a b c hct)
          ((concat_address _ _ _ _ _ _).mpr ⟨htime, (ProductMap.identity_rel _ _).mpr rfl⟩) hb
      have hp : C.True (.first a b c) (address t j) := by
        intro i; fin_cases i <;> assumption
      have hv0 : C.PortTrue (.second a b c) (address t j) 0 :=
        C.edge_rel (.join a b c) ((ProductMap.identity_rel _ _).mpr rfl) hp
      have hv1 : C.PortTrue (.second a b c) (address t j) 1 :=
        C.edge_rel (.right a b c hct hright)
          ((concat_address _ _ _ _ _ _).mpr ⟨htime, hrightrel'⟩) hc
      have hv : C.True (.second a b c) (address t j) := by
        intro i; fin_cases i <;> assumption
      have hs : C.PortTrue (.scalar (F a b c)) (address t j) 0 :=
        C.edge_rel (.output a b c) ((ProductMap.identity_rel _ _).mpr rfl) hv
      have hn' : n = (n - 1) + 1 := by omega
      have hval : evolution F init n j = F a b c := by rw [hn']; rfl
      rw [hval]
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using hs

include hseed in
theorem accepted_iff : (circuit F seedLetter seedDomain accept).Accepted ↔
    ∃ j : Bits d, accept (evolution F init (2 ^ d - 1) j) := by
  constructor
  · rintro ⟨f, a, ha⟩
    have hrel := ProductMap.rel_point ((circuit F seedLetter seedDomain accept).testMap f) a
    obtain ⟨ht, _⟩ := (ProductMap.concat_rel _ _ _ _).mp hrel
    obtain ⟨ht, _⟩ := (ProductMap.singleton_rel _ _ _ _).mp ht
    have hs := port_sound F seedLetter seedDomain accept init hseed (ha 0)
    change f.val = evolution F init (value (time _)) (position _) at hs
    have ht' : value (time ((circuit F seedLetter seedDomain accept).testMap f |>.source a)) = 2 ^ d - 1 := by
      change value (fun i => ((circuit F seedLetter seedDomain accept).testMap f).source a (Fin.castAdd d i)) = _
      rw [ht]; have := value_one d; omega
    rw [ht'] at hs
    exact ⟨_, hs ▸ f.property⟩
  · rintro ⟨j, hj⟩
    let f : {f : A // accept f} := ⟨evolution F init (2 ^ d - 1) j, hj⟩
    let x : Address d := address (fun _ => true) j
    have hrel : ((circuit F seedLetter seedDomain accept).testMap f).Rel x x :=
      (concat_address _ _ _ _ _ _).mpr (by simp only [ProductMap.singleton_rel, ProductMap.identity_rel, and_self])
    obtain ⟨a, ha, _⟩ := (ProductMap.rel_iff _ _ _).mp hrel
    refine ⟨f, a, ?_⟩
    rw [ha]
    have ht : value (fun _ : Fin d => true) = 2 ^ d - 1 := by have := value_one d; omega
    simpa only [ht] using scalar_complete F seedLetter seedDomain accept init hseed (fun _ => true) j

end CellularCircuit

end WLIdentification

end OAI
