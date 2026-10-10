import OAI.Computability.WLIdentification.RejectingMates

namespace OAI

namespace WLIdentification

namespace BufferAlgebra

abbrev Vector := Fin 2 → Bit

def Determined {V : Type} (Q : Set V) (f : V → Bit) : Prop :=
  ∀ v ∈ Q, ∀ w ∈ Q, f v = f w

theorem determined_comp {V W : Type} {Q : Set V} {R : Set W} {f : V → Bit}
    {g : W → Bit} (d : Bit)
    (he : f '' Q = (fun w => d + g w) '' R) :
    Determined Q f ↔ Determined R g := by
  constructor
  · intro h v hv w hw
    obtain ⟨v', hv', ev⟩ := he.symm ▸ (show d + g v ∈ (fun w => d + g w) '' R from ⟨v, hv, rfl⟩)
    obtain ⟨w', hw', ew⟩ := he.symm ▸ (show d + g w ∈ (fun w => d + g w) '' R from ⟨w, hw, rfl⟩)
    exact add_left_cancel (ev.symm.trans ((h v' hv' w' hw').trans ew))
  · intro h v hv w hw
    obtain ⟨v', hv', ev⟩ := he ▸ (show f v ∈ f '' Q from ⟨v, hv, rfl⟩)
    obtain ⟨w', hw', ew⟩ := he ▸ (show f w ∈ f '' Q from ⟨w, hw, rfl⟩)
    exact ev.symm.trans ((congrArg (d + ·) (h v' hv' w' hw')).trans ew)

theorem determined_zero {V : Type} (Q : Set V) : Determined Q (fun _ => 0) :=
  fun _ _ _ _ => rfl

theorem determined_sum {J V : Type} [Fintype J] {Q : Set V} {f : J → V → Bit}
    (h : ∀ j, Determined Q (f j)) : Determined Q (fun v => ∑ j, f j v) := by
  intro v hv w hw
  exact Finset.sum_congr rfl (fun j _ => h j v hv w hw)

theorem subsingleton_of_coordinates {J : Type} {Q : Set (J → Bit)}
    (h : ∀ j, Determined Q (fun v => v j)) : Q.Subsingleton := by
  intro v hv w hw
  funext j
  exact h j v hv w hw

theorem determined_of_subsingleton {V : Type} {Q : Set V}
    (h : Q.Subsingleton) (f : V → Bit) : Determined Q f := by
  intro v hv w hw
  rw [h hv hw]

/-- Arbitrarily shifted private buffers propagate singletonness only forwards. -/
theorem forward {V W : Type} {Q : Set V} {R : Set W} {B : Set Vector}
    {f : V → Bit} {g : W → Bit} (d₁ d₂ d₃ : Bit)
    (h₁ : f '' Q = (fun v => d₁ + v 0) '' B)
    (h₂ : f '' Q = (fun v => d₂ + v 1) '' B)
    (h₃ : (fun v => v 0 + v 1) '' B = (fun w => d₃ + g w) '' R)
    (h : Determined Q f) : Determined R g := by
  apply (determined_comp d₃ h₃).mp
  have ha := (determined_comp d₁ h₁).mp h
  have hb := (determined_comp d₂ h₂).mp h
  intro v hv w hw
  exact congrArg₂ (· + ·) (ha v hv w hw) (hb v hv w hw)

/-- Two copies of one source value cancel, even for nonconstant wire shifts. -/
theorem self_value (x z₁ z₂ d₁ d₂ d₃ : Bit)
    (h₁ : x = d₁ + z₁) (h₂ : x = d₂ + z₂)
    (h₃ : z₁ + z₂ = d₃ + x) : x = d₁ + d₂ + d₃ := by
  linear_combination h₁ + h₂ + h₃

/-- Truth fixes a coordinate to zero; false coordinates remain free. -/
def truthVectors {J : Type} (t : J → Prop) : Set (J → Bit) :=
  {v | ∀ j, t j → v j = 0}

theorem truthVectors_nonempty {J : Type} (t : J → Prop) : (truthVectors t).Nonempty :=
  ⟨fun _ => 0, fun _ _ => rfl⟩

theorem projection_truth {J : Type} [DecidableEq J] (t : J → Prop) [DecidablePred t] (j : J) :
    (fun v => v j) '' truthVectors t = if t j then {0} else Set.univ := by
  classical
  by_cases hj : t j
  · rw [ite_eq_left hj]
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv j hj
    · intro hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨fun _ => 0, fun _ _ => rfl, rfl⟩
  · rw [ite_eq_right hj]
    apply Set.eq_univ_of_forall
    intro x
    refine ⟨Function.update (fun _ => 0) j x, ?_, by simp⟩
    intro i hi
    have hij : i ≠ j := by rintro rfl; exact hj hi
    simp [hij]

theorem sum_truth {J : Type} [Fintype J] (t : J → Prop) [DecidablePred t] :
    (fun v => ∑ j, v j) '' truthVectors t = if ∀ j, t j then {0} else Set.univ := by
  classical
  by_cases ht : ∀ j, t j
  · rw [ite_eq_left ht]
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      simp only [Set.mem_singleton_iff]
      exact Finset.sum_eq_zero (fun j _ => hv j (ht j))
    · intro hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨fun _ => 0, fun _ _ => rfl, by simp⟩
  · rw [ite_eq_right ht]
    obtain ⟨j, hj⟩ := not_forall.mp ht
    apply Set.eq_univ_of_forall
    intro x
    refine ⟨Function.update (fun _ => 0) j x, ?_, ?_⟩
    · intro i hi
      have hij : i ≠ j := by rintro rfl; exact hj hi
      simp [hij]
    · dsimp only
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij; simp [Function.update_of_ne hij]
      · simp

/-- Correlated coordinates keep both input images full while prescribing the sum. -/
def correlated (D : Set Bit) : Set Vector := {v | v 0 + v 1 ∈ D}

theorem correlated_nonempty {D : Set Bit} (hD : D.Nonempty) : (correlated D).Nonempty := by
  obtain ⟨d, hd⟩ := hD
  exact ⟨![0, d], by simpa [correlated] using hd⟩

theorem correlated_projection {D : Set Bit} (hD : D.Nonempty) (j : Fin 2) :
    (fun v => v j) '' correlated D = Set.univ := by
  obtain ⟨d, hd⟩ := hD
  apply Set.eq_univ_of_forall
  intro x
  fin_cases j
  · refine ⟨![x, d + x], ?_, by simp⟩
    simpa [correlated, add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero] using hd
  · refine ⟨![d + x, x], ?_, by simp⟩
    simpa [correlated, add_assoc, CharTwo.add_self_eq_zero] using hd

theorem correlated_sum (D : Set Bit) :
    (fun v => v 0 + v 1) '' correlated D = D := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩; exact hv
  · intro hx
    exact ⟨![0, x], by simpa [correlated] using hx, by simp⟩

end BufferAlgebra

/-- A componentwise injection on a nonempty Boolean product domain.
Values of `mapping` off the domain are immaterial. -/
structure ProductMap (r : ℕ) where
  domain : Fin r → Finset Bool
  nonempty : ∀ i, (domain i).Nonempty
  mapping : Fin r → Bool → Bool
  injective : ∀ i, Set.InjOn (mapping i) {x | x ∈ domain i}

namespace ProductMap
variable {r : ℕ}
abbrev Point (D : ProductMap r) := (i : Fin r) → {b // b ∈ D.domain i}
def source (D : ProductMap r) (a : D.Point) : Fin r → Bool := fun i => (a i).val
def target (D : ProductMap r) (a : D.Point) : Fin r → Bool := fun i => D.mapping i (a i).val

def identity (r : ℕ) : ProductMap r where
  domain _ := Finset.univ
  nonempty _ := ⟨false, Finset.mem_univ _⟩
  mapping _ := id
  injective _ _ _ _ _ h := h

def flip (i : Fin r) : ProductMap r where
  domain _ := Finset.univ
  nonempty _ := ⟨false, Finset.mem_univ _⟩
  mapping j b := if j = i then !b else b
  injective j x _ y _ h := by
    by_cases hj : j = i
    · simpa only [hj, ite_true, Bool.not_not] using congrArg (fun b => !b) h
    · simpa only [hj, ite_false] using h

def identityOn (D : ProductMap r) : ProductMap r where
  domain := D.domain
  nonempty := D.nonempty
  mapping _ := id
  injective _ _ _ _ _ h := h

def ofAddress (a : Fin r → Bool) : (identity r).Point :=
  fun i => ⟨a i, Finset.mem_univ _⟩

theorem source_ofAddress (a : Fin r → Bool) : (identity r).source (ofAddress a) = a := rfl

end ProductMap

structure ProductCircuit (r : ℕ) (P E Z T : Type) where
  pointIndex : P ↪ ℕ
  edgeIndex : E ↪ ℕ
  seedIndex : Z ↪ ℕ
  testIndex : T ↪ ℕ
  dimension : P → ℕ
  dimension_bound : ∀ p, dimension p = 1 ∨ dimension p = 2
  source : E → P
  target : E → P
  port : (e : E) → Fin (dimension (target e))
  edgeMap : E → ProductMap r
  seedType : Z → P
  seed_scalar : ∀ z, dimension (seedType z) = 1
  seedMap : Z → ProductMap r
  testType : T → P
  test_scalar : ∀ t, dimension (testType t) = 1
  testMap : T → ProductMap r

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} (C : ProductCircuit r P E Z T)

inductive PortTrue : (p : P) → (Fin r → Bool) → Fin (C.dimension p) → Prop
  | seed (z : Z) (a : (C.seedMap z).Point) (j : Fin (C.dimension (C.seedType z))) :
      PortTrue (C.seedType z) ((C.seedMap z).source a) j
  | edge (e : E) (a : (C.edgeMap e).Point)
      (h : ∀ j, PortTrue (C.source e) ((C.edgeMap e).source a) j) :
      PortTrue (C.target e) ((C.edgeMap e).target a) (C.port e)

def True (p : P) (a : Fin r → Bool) : Prop := ∀ j, C.PortTrue p a j

def Accepted : Prop := ∃ (t : T) (a : (C.testMap t).Point),
  C.True (C.testType t) ((C.testMap t).source a)

theorem accepted_reseed (zindex : Z ↪ ℕ) :
    ({C with seedIndex := zindex} : ProductCircuit r P E Z T).Accepted ↔ C.Accepted := by
  let D : ProductCircuit r P E Z T := {C with seedIndex := zindex}
  have hp (p : P) (a : Fin r → Bool) (j : Fin (C.dimension p)) :
      D.PortTrue p a j ↔ C.PortTrue p a j := by
    constructor
    · intro h
      induction h using @PortTrue.rec r P E Z T D with
      | seed z a j => exact PortTrue.seed (C := C) z a j
      | edge e a h ih => exact PortTrue.edge (C := C) e a ih
    · intro h
      induction h using @PortTrue.rec r P E Z T C with
      | seed z a j => exact PortTrue.seed (C := D) z a j
      | edge e a h ih => exact PortTrue.edge (C := D) e a ih
  constructor
  · rintro ⟨t,a,h⟩
    exact ⟨t,a,fun j => (hp _ _ j).mp (h j)⟩
  · rintro ⟨t,a,h⟩
    exact ⟨t,a,fun j => (hp _ _ j).mpr (h j)⟩

abbrev Primary (_C : ProductCircuit r P E Z T) := Option P

abbrev primaryDimension : C.Primary → ℕ
  | none => 1
  | some p => C.dimension p

def sumForm (d : ℕ) : (Fin d → Bit) →ₗ[Bit] Bit := ∑ j, LinearMap.proj j

theorem sumForm_apply (d : ℕ) (v : Fin d → Bit) : sumForm d v = ∑ j, v j := by
  simp [sumForm]

inductive Connection where
  | original (e : E)
  | test (t : T)
  | flip (i : Fin r)
  | broadcast (p : P) (j : Fin (C.dimension p))
  | self (p : C.Primary) (j : Fin (C.primaryDimension p))
  | conflict
  deriving Fintype

abbrev connectionSource : C.Connection → C.Primary
  | .original e => some (C.source e)
  | .test t => some (C.testType t)
  | .flip _ => none
  | .broadcast _ _ => none
  | .self p _ => p
  | .conflict => none

abbrev connectionTarget : C.Connection → C.Primary
  | .original e => some (C.target e)
  | .test _ => none
  | .flip _ => none
  | .broadcast p _ => some p
  | .self p _ => p
  | .conflict => none

abbrev connectionMap : C.Connection → ProductMap r
  | .original e => C.edgeMap e
  | .test t => (C.testMap t).identityOn
  | .flip i => .flip i
  | .broadcast _ _ => .identity r
  | .self _ _ => .identity r
  | .conflict => .identity r

abbrev sourceForm (l : C.Connection) : (Fin (C.primaryDimension (C.connectionSource l)) → Bit) →ₗ[Bit] Bit :=
  match l with
  | .original e => sumForm (C.dimension (C.source e))
  | .test t => sumForm (C.dimension (C.testType t))
  | .flip _ => LinearMap.proj (0 : Fin 1)
  | .broadcast _ _ => LinearMap.proj (0 : Fin 1)
  | .self _ j => LinearMap.proj j
  | .conflict => LinearMap.proj (0 : Fin 1)

abbrev targetForm (l : C.Connection) : (Fin (C.primaryDimension (C.connectionTarget l)) → Bit) →ₗ[Bit] Bit :=
  match l with
  | .original e => LinearMap.proj (C.port e)
  | .test _ => LinearMap.proj (0 : Fin 1)
  | .flip _ => LinearMap.proj (0 : Fin 1)
  | .broadcast _ j => LinearMap.proj j
  | .self _ j => LinearMap.proj j
  | .conflict => LinearMap.proj (0 : Fin 1)

inductive RealType where
  | primary (p : C.Primary)
  | buffer (l : C.Connection)
  | dummy
  deriving Fintype

inductive Comparison where
  | seed (z : Z)
  | first (l : C.Connection)
  | second (l : C.Connection)
  | third (l : C.Connection)
  deriving Fintype

abbrev realDimension : C.RealType → ℕ
  | .primary p => C.primaryDimension p
  | .buffer _ => 2
  | .dummy => 1

abbrev comparisonSource : C.Comparison → C.RealType
  | .seed z => .primary (some (C.seedType z))
  | .first l => .primary (C.connectionSource l)
  | .second l => .primary (C.connectionSource l)
  | .third l => .buffer l

abbrev comparisonTarget : C.Comparison → C.RealType
  | .seed _ => .dummy
  | .first l => .buffer l
  | .second l => .buffer l
  | .third l => .primary (C.connectionTarget l)

abbrev comparisonMap : C.Comparison → ProductMap r
  | .seed z => (C.seedMap z).identityOn
  | .first l => (C.connectionMap l).identityOn
  | .second l => (C.connectionMap l).identityOn
  | .third l => C.connectionMap l

abbrev comparisonLeft (e : C.Comparison) :
    (Fin (C.realDimension (C.comparisonSource e)) → Bit) →ₗ[Bit] Bit :=
  match e with
  | .seed z => sumForm (C.dimension (C.seedType z))
  | .first l => C.sourceForm l
  | .second l => C.sourceForm l
  | .third _ => (LinearMap.proj (0 : Fin 2) : (Fin 2 → Bit) →ₗ[Bit] Bit) + LinearMap.proj (1 : Fin 2)

abbrev comparisonRight (e : C.Comparison) :
    (Fin (C.realDimension (C.comparisonTarget e)) → Bit) →ₗ[Bit] Bit :=
  match e with
  | .seed _ => 0
  | .first _ => LinearMap.proj (0 : Fin 2)
  | .second _ => LinearMap.proj (1 : Fin 2)
  | .third l => C.targetForm l

/-- Exactly seeds and three comparisons per private buffer, with two distinct
copies of A's full-product identity self-connection. -/
def connectionIndexValue : C.Connection → ℕ
  | .original e => Nat.pair 0 (C.edgeIndex e)
  | .test t => Nat.pair 1 (C.testIndex t)
  | .flip i => Nat.pair 2 i.val
  | .broadcast p j => Nat.pair 3 (Nat.pair (C.pointIndex p) j.val)
  | .self p j => Nat.pair 4 (Nat.pair (NaturalCode.option C.pointIndex p) j.val)
  | .conflict => Nat.pair 5 0

def connectionIndex : C.Connection ↪ ℕ where
  toFun := C.connectionIndexValue
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp only [connectionIndexValue, Nat.pair_eq_pair, Nat.reduceEqDiff, false_and,
        true_and] at h
    · exact congrArg Connection.original (C.edgeIndex.injective h)
    · exact congrArg Connection.test (C.testIndex.injective h)
    · exact congrArg Connection.flip (Fin.ext h)
    · obtain ⟨hp,hj⟩ := h
      have he := C.pointIndex.injective hp
      subst_vars
      have he := Fin.ext hj
      subst_vars
      rfl
    · obtain ⟨hp,hj⟩ := h
      have he := (NaturalCode.option C.pointIndex).injective hp
      subst_vars
      have he := Fin.ext hj
      subst_vars
      rfl
    · rfl

def realIndexValue : C.RealType → ℕ
  | .primary p => Nat.pair 0 (NaturalCode.option C.pointIndex p)
  | .buffer l => Nat.pair 1 (C.connectionIndex l)
  | .dummy => Nat.pair 2 0

def realIndex : C.RealType ↪ ℕ where
  toFun := C.realIndexValue
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp only [realIndexValue, Nat.pair_eq_pair, Nat.reduceEqDiff, false_and,
        true_and] at h
    · exact congrArg RealType.primary ((NaturalCode.option C.pointIndex).injective h)
    · exact congrArg RealType.buffer (C.connectionIndex.injective h)
    · rfl

def comparisonIndexValue : C.Comparison → ℕ
  | .seed z => Nat.pair 0 (C.seedIndex z)
  | .first l => Nat.pair 1 (C.connectionIndex l)
  | .second l => Nat.pair 2 (C.connectionIndex l)
  | .third l => Nat.pair 3 (C.connectionIndex l)

def comparisonIndex : C.Comparison ↪ ℕ where
  toFun := C.comparisonIndexValue
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp only [comparisonIndexValue, Nat.pair_eq_pair, Nat.reduceEqDiff, false_and,
        true_and] at h
    · exact congrArg Comparison.seed (C.seedIndex.injective h)
    · exact congrArg Comparison.first (C.connectionIndex.injective h)
    · exact congrArg Comparison.second (C.connectionIndex.injective h)
    · exact congrArg Comparison.third (C.connectionIndex.injective h)

def schemas : ComparisonSchemas r C.RealType C.Comparison where
  pointIndex := C.realIndex
  edgeIndex := C.comparisonIndex
  dimension := C.realDimension
  dimension_bound p := by
    cases p with
    | primary p => cases p with
      | none => exact Or.inl rfl
      | some p => exact C.dimension_bound p
    | buffer _ => exact Or.inr rfl
    | dummy => exact Or.inl rfl
  source := C.comparisonSource
  target := C.comparisonTarget
  domain e := (C.comparisonMap e).domain
  domain_nonempty e := (C.comparisonMap e).nonempty
  mapping e i a := (C.comparisonMap e).mapping i a.val
  mapping_injective e i := by
    intro a b h
    exact Subtype.ext ((C.comparisonMap e).injective i a.property b.property h)
  left := C.comparisonLeft
  right := C.comparisonRight

end ProductCircuit

end WLIdentification

end OAI
