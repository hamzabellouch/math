import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Std

namespace OAI

namespace UniqueGamesTheorem.Soundness.ZeroInformation

/-! ## The observation fibre is a Cartesian product -/

section Fibres

variable {P X Y : Type} (hidden : P → Bool) (reveal : P → X → Y) (observed : P → Y)

/-- The complete draw, constrained only by the observations outside the hidden set. -/
def Fibre := {sample : P → X //
  ∀ j, hidden j = false → reveal j (sample j) = observed j}

/-- At hidden positions the draw is unconstrained. -/
def Inside := (j : P) → hidden j = true → X

/-- The remaining part of a draw, satisfying the outside observation. -/
def Outside := {sample : (j : P) → hidden j = false → X //
  ∀ j hj, reveal j (sample j hj) = observed j}

def fibreInside (sample : Fibre hidden reveal observed) : Inside (X := X) hidden :=
  fun j _ => sample.val j

def fibreOutside (sample : Fibre hidden reveal observed) : Outside hidden reveal observed :=
  ⟨fun j _ => sample.val j, sample.property⟩

def assemble (inside : Inside (X := X) hidden) (outside : Outside hidden reveal observed) :
    Fibre hidden reveal observed :=
  ⟨fun j => if hj : hidden j = true then inside j hj else outside.val j (by
      cases h : hidden j
      · rfl
      · exact False.elim (hj h)), by
    intro j hj
    simp only [hj, Bool.false_eq_true, ↓reduceDIte]
    exact outside.property j hj⟩

@[simp] theorem inside_assemble (inside : Inside (X := X) hidden)
    (outside : Outside hidden reveal observed) :
    fibreInside hidden reveal observed (assemble hidden reveal observed inside outside) = inside := by
  funext j hj
  simp [fibreInside, assemble, hj]

@[simp] theorem outside_assemble (inside : Inside (X := X) hidden)
    (outside : Outside hidden reveal observed) :
    fibreOutside hidden reveal observed (assemble hidden reveal observed inside outside) = outside := by
  apply Subtype.ext
  funext j hj
  simp [fibreOutside, assemble, hj]

@[simp] theorem assemble_split (sample : Fibre hidden reveal observed) :
    assemble hidden reveal observed
      (fibreInside hidden reveal observed sample)
      (fibreOutside hidden reveal observed sample) = sample := by
  apply Subtype.ext
  funext j
  simp only [assemble, fibreInside, fibreOutside]
  split <;> rfl

/-- A fibre is in explicit bijection with the product of unrestricted inside draws
and admissible outside draws. This assertion does not posit any independence axiom. -/
theorem fibre_product (sample : Fibre hidden reveal observed) :
    ∃ inside : Inside (X := X) hidden, ∃ outside : Outside hidden reveal observed,
      assemble hidden reveal observed inside outside = sample := by
  exact ⟨fibreInside hidden reveal observed sample,
    fibreOutside hidden reveal observed sample,
    assemble_split hidden reveal observed sample⟩

end Fibres

/-! ## Exact weighted finite counting -/

def mass {A : Type} : List A → (A → Nat) → Nat
  | [], _ => 0
  | a :: rest, w => w a + mass rest w

theorem mass_scale {A : Type} (xs : List A) (w : A → Nat) (c : Nat) :
    mass xs (fun x => c * w x) = c * mass xs w := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih => simp only [mass, ih, Nat.mul_add]

/-- `outsideWeight` may already include the indicator of a fixed observation H=h. -/
theorem rectangular_mass {A B : Type} (outside : List A) (inside : List B)
    (outsideWeight : A → Nat) (insideWeight : B → Nat) :
    mass outside (fun a => mass inside (fun b => outsideWeight a * insideWeight b)) =
      mass outside outsideWeight * mass inside insideWeight := by
  induction outside with
  | nil => simp [mass]
  | cons a outside ih =>
      change mass inside (fun b => outsideWeight a * insideWeight b) +
        mass outside (fun a => mass inside (fun b => outsideWeight a * insideWeight b)) = _
      rw [ih, mass_scale]
      simp only [mass, Nat.add_mul]

/-- The division-free conditional-probability identity. If the observation has
positive mass, division by that mass gives the unchanged inside law. -/
theorem conditional_inside_identity {A B : Type} (outside : List A) (inside : List B)
    (outsideWeight : A → Nat) (insideWeight : B → Nat) (event : B → Bool) :
    mass outside (fun a => mass inside (fun b =>
        outsideWeight a * (if event b then insideWeight b else 0))) *
      mass inside insideWeight =
    mass outside (fun a => mass inside (fun b => outsideWeight a * insideWeight b)) *
      mass inside (fun b => if event b then insideWeight b else 0) := by
  rw [rectangular_mass, rectangular_mass]
  simp only [Nat.mul_assoc]
  rw [Nat.mul_comm (mass inside (fun b => if event b then insideWeight b else 0))]

/-! ## Position-indexed row maps -/

abbrev Bits (R : Type) := R → Bool

def zero {R : Type} : Bits R := fun _ => false

def add {R : Type} (a b : Bits R) : Bits R := fun r => a r ^^ b r

def scale {R : Type} (coefficient : Bits R) (bit : Bool) : Bits R :=
  fun r => coefficient r && bit

@[simp] theorem scale_zero {R : Type} (bit : Bool) :
    scale (zero : Bits R) bit = zero := by
  funext r
  simp [scale, zero]

def rowSum {P R : Type} (positions : List P) (term : P → Bits R) : Bits R :=
  positions.foldr (fun j acc => add (term j) acc) zero

theorem rowSum_congr {P R : Type} (positions : List P) (a b : P → Bits R)
    (h : ∀ j, a j = b j) : rowSum positions a = rowSum positions b := by
  have hab : a = b := funext h
  rw [hab]

/-- Raw row application after pulling back the retained coordinates along π.
`single` records J, and `omega` is indexed by positions, never by names. -/
def pullbackRow {P R : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (indices : P → Fin 3) (homogeneous : Bool) (x : P → Fin 3 → Bool) : Bits R :=
  add (scale zeta0 homogeneous) (rowSum positions fun j =>
    if single j then scale (omega j) (x j (indices j))
    else add (scale (zeta1 j) (x j 0)) (scale (zeta2 j) (x j 1)))

/-- Changing an index where its position coefficient is zero does not change the
entire row map. This is an equality for all ambient coordinates, so also on E_U. -/
theorem pullbackRow_index_independent {P R : Type} (positions : List P)
    (single : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (i i' : P → Fin 3)
    (agrees : ∀ j, single j = true → omega j ≠ zero → i j = i' j)
    (homogeneous : Bool) (x : P → Fin 3 → Bool) :
    pullbackRow positions single zeta0 zeta1 zeta2 omega i homogeneous x =
      pullbackRow positions single zeta0 zeta1 zeta2 omega i' homogeneous x := by
  unfold pullbackRow
  congr 1
  apply rowSum_congr
  intro j
  cases hs : single j
  · simp
  · simp only [↓reduceIte]
    by_cases hz : omega j = zero
    · simp [hz]
    · rw [agrees j hs hz]

/-- Distinct occurrence names recover the retained index at all nonzero positions.
Consequently revealing outside (occurrence,name) pairs supplies exactly the indices
needed by the first player; inside names and indices are unnecessary. -/
theorem pullbackRow_from_outside_names {P R O N : Type} (positions : List P)
    (single : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (occurrences : P → O) (name : O → Fin 3 → N)
    (distinct : ∀ o i i', name o i = name o i' → i = i')
    (i i' : P → Fin 3)
    (sameNames : ∀ j, single j = true → omega j ≠ zero →
      name (occurrences j) (i j) = name (occurrences j) (i' j))
    (homogeneous : Bool) (x : P → Fin 3 → Bool) :
    pullbackRow positions single zeta0 zeta1 zeta2 omega i homogeneous x =
      pullbackRow positions single zeta0 zeta1 zeta2 omega i' homogeneous x := by
  apply pullbackRow_index_independent
  intro j hj hz
  exact distinct (occurrences j) (i j) (i' j) (sameNames j hj hz)

/-- In particular, substituting the equation for a retained third bit cannot leak
the hidden right-hand side through a zero coefficient. -/
theorem zero_third_bit {R : Type} (rhs homogeneous x1 x2 : Bool) :
    scale (zero : Bits R) ((rhs && homogeneous) ^^ x1 ^^ x2) = zero := by
  exact scale_zero _

/-! ## Complete private-input reconstruction -/

/-- A raw row function on ambient first-question coordinates. Restricting it to
the equation subspace gives the supplied map `Z_B π`. -/
abbrev FirstRow (P R : Type) := Bool → (P → Fin 3 → Bool) → Bits R

/-- A raw row function on ambient partner coordinates. -/
abbrev SecondRow (P R : Type) :=
  Bool → (P → Fin 3 → Bool) → (P → Bool) → Bits R

structure FirstInput (P R O : Type) where
  question : P → O
  row : FirstRow P R

/-- `Sum.inl o` records a full occurrence and `Sum.inr n` a single named bit.
The summand tag preserves the set J without exposing any retained index. -/
structure SecondInput (P R O N : Type) where
  question : P → Sum O N
  row : SecondRow P R

def partnerQuestion {P O N : Type} (single : P → Bool) (occurrences : P → O)
    (names : P → N) : P → Sum O N :=
  fun j => if single j then .inr (names j) else .inl (occurrences j)

def partnerRow {P R : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R) : SecondRow P R :=
  fun homogeneous x y => add (scale zeta0 homogeneous) (rowSum positions fun j =>
    if single j then scale (omega j) (y j)
    else add (scale (zeta1 j) (x j 0)) (scale (zeta2 j) (x j 1)))

/-- The raw formula really is the pullback under the retained-coordinate projection. -/
theorem partnerRow_pullback {P R : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R) (indices : P → Fin 3)
    (homogeneous : Bool) (x : P → Fin 3 → Bool) :
    partnerRow positions single zeta0 zeta1 zeta2 omega homogeneous x
        (fun j => x j (indices j)) =
      pullbackRow positions single zeta0 zeta1 zeta2 omega indices homogeneous x := rfl

def firstInput {P R O : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (occurrences : P → O) (indices : P → Fin 3) : FirstInput P R O :=
  ⟨occurrences, pullbackRow positions single zeta0 zeta1 zeta2 omega indices⟩

def secondInput {P R O N : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (occurrences : P → O) (names : P → N) : SecondInput P R O N :=
  ⟨partnerQuestion single occurrences names,
    partnerRow positions single zeta0 zeta1 zeta2 omega⟩

/-- A total fixed decoder for a retained index. On supported (o,n) it is uniquely
determined by the distinctness of the three names. -/
noncomputable def decodeIndex {O N : Type} (name : O → Fin 3 → N)
    (occurrence : O) (n : N) : Fin 3 := by
  classical
  exact if h : ∃ i, name occurrence i = n then Classical.choose h else 0

theorem decodeIndex_name {O N : Type} (name : O → Fin 3 → N)
    (distinct : ∀ o i i', name o i = name o i' → i = i') (o : O) (i : Fin 3) :
    decodeIndex name o (name o i) = i := by
  classical
  unfold decodeIndex
  have he : ∃ i', name o i' = name o i := ⟨i, rfl⟩
  simp only [he, ↓reduceDIte]
  exact distinct o _ i (Classical.choose_spec he)

def reconstructQuestion {P X : Type} (hidden : P → Bool) (inside outside : P → X) : P → X :=
  fun j => if hidden j then inside j else outside j

theorem reconstructQuestion_actual {P X : Type} (hidden : P → Bool)
    (actual outside : P → X) (houtside : ∀ j, hidden j = false → outside j = actual j) :
    reconstructQuestion hidden actual outside = actual := by
  funext j
  cases hj : hidden j
  · simp [reconstructQuestion, hj, houtside j hj]
  · simp [reconstructQuestion, hj]

/-- The first reconstruction receives only fixed outside occurrence/name data,
the fixed raw coefficients, and the inside occurrence draw. -/
noncomputable def reconstructFirst {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (name : O → Fin 3 → N) (insideOccurrences outsideOccurrences : P → O)
    (outsideNames : P → N) : FirstInput P R O :=
  firstInput positions single zeta0 zeta1 zeta2 omega
    (reconstructQuestion hidden insideOccurrences outsideOccurrences)
    (fun j => decodeIndex name (outsideOccurrences j) (outsideNames j))

theorem first_input_reconstruction {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (hidden_zero : ∀ j, hidden j = true → omega j = zero)
    (name : O → Fin 3 → N)
    (distinct : ∀ o i i', name o i = name o i' → i = i')
    (occurrences outsideOccurrences : P → O) (indices : P → Fin 3)
    (outsideNames : P → N)
    (houtsideO : ∀ j, hidden j = false → outsideOccurrences j = occurrences j)
    (houtsideN : ∀ j, hidden j = false → outsideNames j = name (occurrences j) (indices j)) :
    reconstructFirst positions single hidden zeta0 zeta1 zeta2 omega name
        occurrences outsideOccurrences outsideNames =
      firstInput positions single zeta0 zeta1 zeta2 omega occurrences indices := by
  unfold reconstructFirst firstInput
  rw [reconstructQuestion_actual hidden occurrences outsideOccurrences houtsideO]
  congr 1
  funext homogeneous x
  apply pullbackRow_index_independent
  intro j _ hz
  have hj : hidden j = false := by
    cases hh : hidden j
    · rfl
    · exact False.elim (hz (hidden_zero j hh))
  rw [houtsideO j hj, houtsideN j hj]
  exact decodeIndex_name name distinct (occurrences j) (indices j)

/-- The second reconstruction receives no inside occurrence: only inside names. -/
def reconstructSecond {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (outsideOccurrences : P → O) (insideNames outsideNames : P → N) : SecondInput P R O N :=
  secondInput positions single zeta0 zeta1 zeta2 omega outsideOccurrences
    (reconstructQuestion hidden insideNames outsideNames)

theorem second_input_reconstruction {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (hidden_single : ∀ j, hidden j = true → single j = true)
    (occurrences outsideOccurrences : P → O) (names outsideNames : P → N)
    (houtsideO : ∀ j, hidden j = false → outsideOccurrences j = occurrences j)
    (houtsideN : ∀ j, hidden j = false → outsideNames j = names j) :
    reconstructSecond positions single hidden zeta0 zeta1 zeta2 omega
        outsideOccurrences names outsideNames =
      secondInput positions single zeta0 zeta1 zeta2 omega occurrences names := by
  unfold reconstructSecond secondInput
  rw [reconstructQuestion_actual hidden names outsideNames houtsideN]
  congr 1
  funext j
  unfold partnerQuestion
  cases hs : single j
  · have hj : hidden j = false := by
      cases hh : hidden j
      · rfl
      · have contradiction := hidden_single j hh
        rw [hs] at contradiction
        contradiction
    simp [houtsideO j hj]
  · simp

/-- The first equation subspace is determined by its occurrence question alone. -/
def FirstPoint {P O : Type} (rhs : O → Bool) (question : P → O) :=
  {point : Bool × (P → Fin 3 → Bool) // ∀ j,
    (point.2 j 0 ^^ point.2 j 1 ^^ point.2 j 2) = (rhs (question j) && point.1)}

/-- At single positions the partner space has a free bit and no occurrence or rhs.
Unused ambient coordinates are fixed to zero, giving a canonical embedding of
the position-dependent coordinate space rather than extra degrees of freedom. -/
def SecondPoint {P O N : Type} (rhs : O → Bool) (question : P → Sum O N) :=
  {point : Bool × (P → Fin 3 → Bool) × (P → Bool) // ∀ j,
    match question j with
    | .inl o =>
      (point.2.1 j 0 ^^ point.2.1 j 1 ^^ point.2.1 j 2) = (rhs o && point.1) ∧
      point.2.2 j = false
    | .inr _ => ∀ i, point.2.1 j i = false}

def FirstInput.suppliedMap {P R O : Type} (input : FirstInput P R O) (rhs : O → Bool) :
    FirstPoint rhs input.question → Bits R :=
  fun point => input.row point.val.1 point.val.2

def SecondInput.suppliedMap {P R O N : Type} (input : SecondInput P R O N) (rhs : O → Bool) :
    SecondPoint rhs input.question → Bits R :=
  fun point => input.row point.val.1 point.val.2.1 point.val.2.2

def projectFull {P : Type} (single : P → Bool) (x : P → Fin 3 → Bool) :
    P → Fin 3 → Bool :=
  fun j i => if single j then false else x j i

def projectSingles {P : Type} (single : P → Bool) (indices : P → Fin 3)
    (x : P → Fin 3 → Bool) : P → Bool :=
  fun j => if single j then x j (indices j) else false

def partnerProjection {P O N : Type} (single : P → Bool) (rhs : O → Bool)
    (occurrences : P → O) (names : P → N) (indices : P → Fin 3)
    (point : FirstPoint rhs occurrences) :
    SecondPoint rhs (partnerQuestion single occurrences names) :=
  ⟨(point.val.1, projectFull single point.val.2, projectSingles single indices point.val.2), by
    intro j
    cases hs : single j
    · simp only [partnerQuestion, hs, Bool.false_eq_true, ↓reduceIte,
        projectFull, projectSingles]
      exact ⟨point.property j, True.intro⟩
    · simp [partnerQuestion, hs, projectFull]⟩

theorem partnerRow_project {P R : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R) (indices : P → Fin 3)
    (homogeneous : Bool) (x : P → Fin 3 → Bool) :
    partnerRow positions single zeta0 zeta1 zeta2 omega homogeneous
        (projectFull single x) (projectSingles single indices x) =
      pullbackRow positions single zeta0 zeta1 zeta2 omega indices homogeneous x := by
  unfold partnerRow pullbackRow
  congr 1
  apply rowSum_congr
  intro j
  cases hs : single j <;> simp [hs, projectFull, projectSingles]

theorem supplied_map_pullback {P R O N : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R) (rhs : O → Bool)
    (occurrences : P → O) (names : P → N) (indices : P → Fin 3)
    (point : FirstPoint rhs occurrences) :
    (secondInput positions single zeta0 zeta1 zeta2 omega occurrences names).suppliedMap rhs
        (partnerProjection single rhs occurrences names indices point) =
      (firstInput positions single zeta0 zeta1 zeta2 omega occurrences indices).suppliedMap rhs point := by
  exact partnerRow_project positions single zeta0 zeta1 zeta2 omega indices point.val.1 point.val.2

end UniqueGamesTheorem.Soundness.ZeroInformation

open scoped BigOperators

namespace UniqueGamesTheorem.Soundness.ConditionalIncidences

noncomputable section

abbrev PositionInside {P : Type} (K : Finset P) := {j : P // j ∈ K}
abbrev PositionOutside {P : Type} (K : Finset P) := {j : P // j ∉ K}
abbrev Draw (P O : Type) := P → O × Fin 3
abbrev InsideDraw {P : Type} (K : Finset P) (O : Type) := PositionInside K → O × Fin 3

def incidence {O N : Type} (name : O → Fin 3 → N) (draw : O × Fin 3) : O × N :=
  (draw.1, name draw.1 draw.2)

def insideDraw {P O : Type} (K : Finset P) (sample : Draw P O) : InsideDraw K O :=
  fun j => sample j.val

def outsideRecord {P O N : Type} (K : Finset P) (name : O → Fin 3 → N)
    (sample : Draw P O) : PositionOutside K → O × N :=
  fun j => incidence name (sample j.val)

abbrev ObservationFibre {P O N : Type} (K : Finset P) (name : O → Fin 3 → N)
    (observed : PositionOutside K → O × N) :=
  {sample : Draw P O // outsideRecord K name sample = observed}

abbrev OutsideFibre {P O N : Type} (K : Finset P) (name : O → Fin 3 → N)
    (observed : PositionOutside K → O × N) :=
  {sample : PositionOutside K → O × Fin 3 //
    (fun j => incidence name (sample j)) = observed}

instance observationFibreFintype {P O N : Type} [Fintype P] [Fintype O]
    (K : Finset P) (name : O → Fin 3 → N) (observed : PositionOutside K → O × N) :
    Fintype (ObservationFibre K name observed) := Fintype.ofFinite _

instance outsideFibreFintype {P O N : Type} [Fintype P] [Fintype O]
    (K : Finset P) (name : O → Fin 3 → N) (observed : PositionOutside K → O × N) :
    Fintype (OutsideFibre K name observed) := Fintype.ofFinite _

/-- The actual observation fibre, not an assumed rectangular probability law. -/
def observationFibreEquiv {P O N : Type} [DecidableEq P]
    (K : Finset P) (name : O → Fin 3 → N)
    (observed : PositionOutside K → O × N) :
    ObservationFibre K name observed ≃ InsideDraw K O × OutsideFibre K name observed where
  toFun sample :=
    (insideDraw K sample.val, ⟨fun j => sample.val j.val, sample.property⟩)
  invFun pieces :=
    ⟨fun j => if hj : j ∈ K then pieces.1 ⟨j, hj⟩ else pieces.2.val ⟨j, hj⟩, by
      funext j
      simp only [outsideRecord, j.property, ↓reduceDIte]
      exact congrFun pieces.2.property j⟩
  left_inv sample := by
    apply Subtype.ext
    funext j
    simp only [insideDraw]
    split <;> rfl
  right_inv pieces := by
    apply Prod.ext
    · funext j
      simp [insideDraw, j.property]
    · apply Subtype.ext
      funext j
      simp [j.property]

def average {A : Type} [Fintype A] (f : A → ℚ) : ℚ :=
  (∑ a, f a) / Fintype.card A

theorem average_equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℚ) :
    average (fun a => f (e a)) = average f := by
  unfold average
  rw [e.sum_comp, Fintype.card_congr e]

/-- Cancelling the finite nonempty outside fibre gives a normalized equality. -/
theorem average_product_left {A B : Type} [Fintype A] [Fintype B]
    (hB : Fintype.card B ≠ 0) (f : A → ℚ) :
    average (fun ab : A × B => f ab.1) = average f := by
  unfold average
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.mul_sum]
  have hBq : (Fintype.card B : ℚ) ≠ 0 := by exact_mod_cast hB
  rw [mul_comm (Fintype.card A : ℚ)]
  exact mul_div_mul_left _ _ hBq

/-- Uniform sampling from the actual finite product is independent sampling. -/
theorem average_product_mul {A B : Type} [Fintype A] [Fintype B]
    (f : A → ℚ) (g : B → ℚ) :
    average (fun ab : A × B => f ab.1 * g ab.2) = average f * average g := by
  unfold average
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp only [Fintype.card_prod, Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

/-- The uniform function sample is the product of its uniform coordinate laws. -/
theorem average_coordinate_product {A X : Type} [Fintype A] [DecidableEq A] [Fintype X]
    (f : A → X → ℚ) :
    average (fun sample : A → X => ∏ a, f a (sample a)) = ∏ a, average (f a) := by
  unfold average
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_pi, Nat.cast_prod]
  exact (Finset.prod_div_distrib _ _).symm

/-- This is the usual conditional-expectation ratio in a uniform finite space:
the numerator and event probability are both divided by the full sample count. -/
theorem uniform_conditional_ratio {A : Type} [Fintype A]
    (p : A → Prop) [Fintype {a // p a}]
    (hpos : 0 < Fintype.card {a // p a}) (f : {a // p a} → ℚ) :
    ((∑ a, f a) / (Fintype.card A : ℚ)) /
        ((Fintype.card {a // p a} : ℚ) / Fintype.card A) = average f := by
  have hA : Fintype.card A ≠ 0 :=
    Nat.ne_of_gt (Nat.lt_of_lt_of_le hpos (Fintype.card_subtype_le p))
  have hAq : (Fintype.card A : ℚ) ≠ 0 := by exact_mod_cast hA
  exact div_div_div_cancel_right₀ hAq _ _

section ConditionalLaw

variable {P O N : Type} [Fintype P] [DecidableEq P] [Fintype O]

/-- Exact finite conditional expectation for *every* function of inside draws.
The denominator is the cardinality of the supported observation fibre. -/
theorem conditional_inside_average (K : Finset P) (name : O → Fin 3 → N)
    (observed : PositionOutside K → O × N)
    (hpos : 0 < Fintype.card (ObservationFibre K name observed))
    (f : InsideDraw K O → ℚ) :
    average (fun sample : ObservationFibre K name observed => f (insideDraw K sample.val)) =
      average f := by
  let e := observationFibreEquiv K name observed
  have hcard : Fintype.card (ObservationFibre K name observed) =
      Fintype.card (InsideDraw K O) * Fintype.card (OutsideFibre K name observed) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  have hout : Fintype.card (OutsideFibre K name observed) ≠ 0 := by
    intro hz
    rw [hcard, hz, Nat.mul_zero] at hpos
    exact (Nat.lt_irrefl 0) hpos
  calc
    average (fun sample : ObservationFibre K name observed => f (insideDraw K sample.val)) =
        average (fun pieces : InsideDraw K O × OutsideFibre K name observed => f pieces.1) :=
      average_equiv e (fun pieces => f pieces.1)
    _ = average f := average_product_left hout f

/-- Pushing the fresh occurrence/slot draws through (o,i) ↦ (o,vᵢ(o)) gives
exactly the repeated incidence law, with no distinct-name assumption needed. -/
theorem conditional_incidence_average (K : Finset P) (name : O → Fin 3 → N)
    (observed : PositionOutside K → O × N)
    (hpos : 0 < Fintype.card (ObservationFibre K name observed))
    (f : (PositionInside K → O × N) → ℚ) :
    average (fun sample : ObservationFibre K name observed =>
      f (fun j => incidence name (sample.val j.val))) =
    average (fun fresh : InsideDraw K O => f (fun j => incidence name (fresh j))) := by
  exact conditional_inside_average K name observed hpos
    (fun fresh => f (fun j => incidence name (fresh j)))

end ConditionalLaw

/-- None is ζ₀; the left summand gives two coefficients per full position;
the right summand gives one coefficient per single position. -/
abbrev RawSlot {P : Type} (J : Finset P) :=
  Option ((PositionOutside J × Fin 2) ⊕ PositionInside J)

abbrev RawCoefficients {P : Type} (J : Finset P) (D : Type) := RawSlot J → D

def zeroSet {P D : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (gamma : RawCoefficients J D) : Finset P :=
  J.attach.filter (fun j => gamma (some (.inr j)) = 0) |>.map ⟨Subtype.val, Subtype.val_injective⟩

theorem mem_zeroSet {P D : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (gamma : RawCoefficients J D) (j : P) :
    j ∈ zeroSet J gamma ↔ ∃ hj : j ∈ J, gamma (some (.inr ⟨j, hj⟩)) = 0 := by
  simp [zeroSet]

abbrev RawSample {P : Type} (J : Finset P) (D O : Type) :=
  RawCoefficients J D × Draw P O

/-- H fixes gamma and the outside incidence pairs. K is a deterministic function
of gamma, so including K explicitly in H gives precisely this same event. -/
abbrev RawObservationFibre {P D O N : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N) :=
  {sample : RawSample J D O // sample.1 = gamma ∧
    outsideRecord (zeroSet J gamma) name sample.2 = observed}

instance rawObservationFibreFintype {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D] [Fintype O]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N) :
    Fintype (RawObservationFibre J name gamma observed) := Fintype.ofFinite _

def rawObservationFibreEquiv {P D O N : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N) :
    RawObservationFibre J name gamma observed ≃
      ObservationFibre (zeroSet J gamma) name observed where
  toFun sample := ⟨sample.val.2, sample.property.2⟩
  invFun sample := ⟨(gamma, sample.val), rfl, sample.property⟩
  left_inv sample := by
    apply Subtype.ext
    exact Prod.ext sample.property.1.symm rfl
  right_inv sample := rfl

/-- Lemma 6.7's conditional product law in the actual independent raw sampling
space, with normalized rational expectations. No independence is a hypothesis. -/
theorem raw_conditional_inside_average {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D] [Fintype O] [DecidableEq O] [DecidableEq N]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (hpos : 0 < Fintype.card (RawObservationFibre J name gamma observed))
    (f : InsideDraw (zeroSet J gamma) O → ℚ) :
    average (fun sample : RawObservationFibre J name gamma observed =>
      f (insideDraw (zeroSet J gamma) sample.val.2)) = average f := by
  let e := rawObservationFibreEquiv J name gamma observed
  have hpos' : 0 < Fintype.card (ObservationFibre (zeroSet J gamma) name observed) := by
    rwa [Fintype.card_congr e] at hpos
  calc
    average (fun sample : RawObservationFibre J name gamma observed =>
        f (insideDraw (zeroSet J gamma) sample.val.2)) =
      average (fun sample : ObservationFibre (zeroSet J gamma) name observed =>
        f (insideDraw (zeroSet J gamma) sample.val)) := by
      exact average_equiv e (fun sample : ObservationFibre (zeroSet J gamma) name observed =>
        f (insideDraw (zeroSet J gamma) sample.val))
    _ = average f := conditional_inside_average _ name observed hpos' f

/-- The same exact law expressed as the conditional expectation ratio in the
whole raw sample space. Positive probability is represented by a nonempty fibre. -/
theorem raw_conditional_ratio {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D] [Fintype O] [DecidableEq O] [DecidableEq N]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (hpos : 0 < Fintype.card (RawObservationFibre J name gamma observed))
    (f : InsideDraw (zeroSet J gamma) O → ℚ) :
    ((∑ sample : RawObservationFibre J name gamma observed,
        f (insideDraw (zeroSet J gamma) sample.val.2)) / Fintype.card (RawSample J D O)) /
      ((Fintype.card (RawObservationFibre J name gamma observed) : ℚ) /
        Fintype.card (RawSample J D O)) = average f := by
  rw [uniform_conditional_ratio _ hpos]
  exact raw_conditional_inside_average J name gamma observed hpos f

/-- The pushed-forward product incidence law at K, stated for an arbitrary
joint observable, rather than only individual coordinate marginals. -/
theorem raw_conditional_incidence_average {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D] [Fintype O] [DecidableEq O] [DecidableEq N]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (hpos : 0 < Fintype.card (RawObservationFibre J name gamma observed))
    (f : (PositionInside (zeroSet J gamma) → O × N) → ℚ) :
    average (fun sample : RawObservationFibre J name gamma observed =>
      f (fun j => incidence name (sample.val.2 j.val))) =
    average (fun fresh : InsideDraw (zeroSet J gamma) O => f (fun j => incidence name (fresh j))) := by
  exact raw_conditional_inside_average J name gamma observed hpos
    (fun fresh => f (fun j => incidence name (fresh j)))

/-- Factorization for arbitrary per-position test functions makes the product
claim explicit. Repeated names across different positions are fully permitted. -/
theorem raw_conditional_product_incidence {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D] [Fintype O] [DecidableEq O] [DecidableEq N]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (hpos : 0 < Fintype.card (RawObservationFibre J name gamma observed))
    (f : PositionInside (zeroSet J gamma) → O × N → ℚ) :
    average (fun sample : RawObservationFibre J name gamma observed =>
      ∏ j, f j (incidence name (sample.val.2 j.val))) =
    ∏ j, average (fun fresh : O × Fin 3 => f j (incidence name fresh)) := by
  calc
    _ = average (fun fresh : InsideDraw (zeroSet J gamma) O =>
        ∏ j, f j (incidence name (fresh j))) :=
      raw_conditional_inside_average J name gamma observed hpos
        (fun fresh => ∏ j, f j (incidence name (fresh j)))
    _ = _ := average_coordinate_product (fun j fresh => f j (incidence name fresh))

end

end UniqueGamesTheorem.Soundness.ConditionalIncidences

end OAI
