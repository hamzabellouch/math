import Mathlib
import OAI.Computability.MaxCut.Games.Information

namespace OAI

namespace MaxCutGames.Soundness.IncidenceExtraction

abbrev Triple := Fin 3 → Bool

def xorTriple (x : Triple) : Bool := (x 0 ^^ x 1) ^^ x 2

structure Incidence (Occurrence Name : Type) where
  name : Occurrence → Fin 3 → Name
  rhs : Occurrence → Bool

def Incidence.accepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (i : Fin 3)
    (a : Triple) (b : Bool) : Prop :=
  xorTriple a = g.rhs o ∧ a i = b

/-- The incidence predicate as a game on the actual questions `(o,n)`, with the
    retained slot left internal to the verifier. -/
def Incidence.namedAccepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (n : Name)
    (a : Triple) (b : Bool) : Prop :=
  ∃ i, g.name o i = n ∧ g.accepts o i a b

theorem Incidence.accepts_implies_namedAccepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (i : Fin 3)
    (a : Triple) (b : Bool) (h : g.accepts o i a b) :
    g.namedAccepts o (g.name o i) a b :=
  ⟨i, rfl, h⟩

/-- Distinct names make the named-variable predicate equivalent to the sampled
    retained-slot predicate, without revealing that slot to either strategy. -/
theorem Incidence.namedAccepts_iff_accepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (o : Occurrence) (i : Fin 3) (a : Triple) (b : Bool) :
    g.namedAccepts o (g.name o i) a b ↔ g.accepts o i a b := by
  constructor
  · rintro ⟨j, hname, h⟩
    have hji := distinct o j i hname
    simpa [hji] using h
  · exact g.accepts_implies_namedAccepts o i a b

structure FullPoint (Position : Type) where
  homogeneous : Bool
  coords : Position → Triple

def FullPoint.valid {Position Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (e : FullPoint Position) : Prop :=
  ∀ j, xorTriple (e.coords j) = (g.rhs (u j) && e.homogeneous)

structure PartnerPoint (Position : Type) where
  homogeneous : Bool
  single : Position → Bool

/- Only the single positions matter to the extracted incidence game. -/
def AugmentedAccepts {Position Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (active : Position → Prop) (slot : Position → Fin 3)
    (eA : FullPoint Position) (eB : PartnerPoint Position) : Prop :=
  eA.valid g u ∧ eA.homogeneous = true ∧ eB.homogeneous = true ∧
  ∀ j, active j → eA.coords j (slot j) = eB.single j

def RepeatedAccepts {Position Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (slot : Position → Fin 3) (inside : Position → Prop)
    (answerA : Position → Triple) (answerB : Position → Bool) : Prop :=
  ∀ j, inside j → g.accepts (u j) (slot j) (answerA j) (answerB j)

/-- Acceptance of the augmented projection game implies acceptance of every
    incidence coordinate in any subset of the active positions. -/
theorem augmented_accepts_implies_repeated_accepts
    {Position Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (active inside : Position → Prop) (slot : Position → Fin 3)
    (eA : FullPoint Position) (eB : PartnerPoint Position)
    (hinside : ∀ j, inside j → active j)
    (haccept : AugmentedAccepts g u active slot eA eB) :
    RepeatedAccepts g u slot inside eA.coords eB.single := by
  obtain ⟨hvalid, hone, _, hagree⟩ := haccept
  intro j hj
  constructor
  · have heq := hvalid j
    simpa [hone] using heq
  · exact hagree j (hinside j hj)

/-- The same containment stated on the occurrence/name question vectors actually
    given to the two repeated-game players. -/
theorem augmented_accepts_implies_named_repeated_accepts
    {Position RepeatPosition Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (active : Position → Prop) (slot : Position → Fin 3)
    (embed : RepeatPosition → Position)
    (eA : FullPoint Position) (eB : PartnerPoint Position)
    (hinside : ∀ r, active (embed r))
    (haccept : AugmentedAccepts g u active slot eA eB) :
    ∀ r, g.namedAccepts (u (embed r))
      (g.name (u (embed r)) (slot (embed r)))
      (eA.coords (embed r)) (eB.single (embed r)) := by
  intro r
  apply g.accepts_implies_namedAccepts
  obtain ⟨hvalid, hone, _, hagree⟩ := haccept
  constructor
  · have heq := hvalid (embed r)
    simpa [hone] using heq
  · exact hagree (embed r) (hinside r)

/-!
The next definitions separate local strategies from arbitrary joint strategies.
Each question reconstruction and each answer extraction has access to only one
player's question. A value conditioned on by an analysis may occur as a fixed
parameter of a `LocalSimulation`; it cannot become an additional random input.
-/

structure Game (QA QB A B : Type) where
  accepts : QA → QB → A → B → Prop

structure Strategies (QA QB A B : Type) where
  first : QA → A
  second : QB → B

def Strategies.wins {QA QB A B : Type} (s : Strategies QA QB A B)
    (g : Game QA QB A B) (qa : QA) (qb : QB) : Prop :=
  g.accepts qa qb (s.first qa) (s.second qb)

structure LocalSimulation
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    (inner : Game InnerQA InnerQB InnerA InnerB)
    (outer : Game OuterQA OuterQB OuterA OuterB) where
  questionA : InnerQA → OuterQA
  questionB : InnerQB → OuterQB
  answerA : InnerQA → OuterA → InnerA
  answerB : InnerQB → OuterB → InnerB
  sound : ∀ qa qb a b,
    outer.accepts (questionA qa) (questionB qb) a b →
    inner.accepts qa qb (answerA qa a) (answerB qb b)

def LocalSimulation.induced
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (s : Strategies OuterQA OuterQB OuterA OuterB) :
    Strategies InnerQA InnerQB InnerA InnerB where
  first qa := r.answerA qa (s.first (r.questionA qa))
  second qb := r.answerB qb (s.second (r.questionB qb))

/-- A local simulation transports every deterministic strategy and contains
    its winning event pointwise. No shared access to the questions is used. -/
theorem LocalSimulation.induced_wins
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (s : Strategies OuterQA OuterQB OuterA OuterB)
    (qa : InnerQA) (qb : InnerQB)
    (hwins : s.wins outer (r.questionA qa) (r.questionB qb)) :
    (r.induced s).wins inner qa qb :=
  r.sound qa qb (s.first (r.questionA qa)) (s.second (r.questionB qb)) hwins

/-- Fixing strategy randomness gives another local deterministic strategy;
    the simulation proof applies to every seed, before any averaging. -/
theorem LocalSimulation.seeded_induced_wins
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB Seed : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (strategy : Seed → Strategies OuterQA OuterQB OuterA OuterB)
    (seed : Seed) (qa : InnerQA) (qb : InnerQB)
    (hwins : (strategy seed).wins outer (r.questionA qa) (r.questionB qb)) :
    (r.induced (strategy seed)).wins inner qa qb :=
  r.induced_wins (strategy seed) qa qb hwins

end MaxCutGames.Soundness.IncidenceExtraction

/-!
This bridge connects the concrete partner projection to the actual equation/name
predicate of the incidence game. It uses no probabilistic or analytic hypotheses.
-/

namespace MaxCutGames.Soundness.ConcreteExtraction

open PartnerProjection IncidenceExtraction

def slotIndex : PartnerProjection.Slot → Fin 3
  | .first => 0
  | .second => 1
  | .third => 2

def tripleCoordinates (x : PartnerProjection.Triple) : IncidenceExtraction.Triple :=
  fun i => if i = 0 then x.first else if i = 1 then x.second else x.third

theorem parity_coordinates (x : PartnerProjection.Triple) :
    IncidenceExtraction.xorTriple (tripleCoordinates x) = PartnerProjection.parity x := rfl

theorem retained_coordinates (x : PartnerProjection.Triple) (i : PartnerProjection.Slot) :
    tripleCoordinates x (slotIndex i) = PartnerProjection.retained i x := by
  cases i <;> rfl

def fullPoint {P : Type} {rhs : P → Bool}
    (x : PartnerProjection.SourcePoint rhs) : IncidenceExtraction.FullPoint P :=
  ⟨x.homogeneous, fun j => tripleCoordinates (x.coordinates j)⟩

def partnerPoint {P : Type} {rhs active : P → Bool}
    (x : PartnerProjection.PartnerPoint rhs active) : IncidenceExtraction.PartnerPoint P :=
  ⟨x.homogeneous, x.single⟩

/-- Concrete projection acceptance implies the coordinate-level acceptance
    relation used to extract a repeated incidence strategy. -/
theorem actual_projection_accepts
    {P O N : Type} (g : IncidenceExtraction.Incidence O N) (u : P → O)
    (active : P → Bool) (slot : P → PartnerProjection.Slot)
    (x : PartnerProjection.SourcePoint (fun j => g.rhs (u j)))
    (y : PartnerProjection.PartnerPoint (fun j => g.rhs (u j)) active)
    (hone : x.homogeneous = true)
    (hproject : PartnerProjection.project (fun j => g.rhs (u j)) active slot x = y) :
    IncidenceExtraction.AugmentedAccepts g u (fun j => active j = true)
      (fun j => slotIndex (slot j)) (fullPoint x) (partnerPoint y) := by
  subst y
  constructor
  · intro j
    exact x.valid j
  constructor
  · exact hone
  constructor
  · exact hone
  intro j hj
  change tripleCoordinates (x.coordinates j) (slotIndex (slot j)) =
    (if active j then PartnerProjection.retained (slot j) (x.coordinates j) else false)
  rw [hj]
  exact retained_coordinates _ _

theorem actual_projection_implies_named_repetition
    {P R O N : Type} (g : IncidenceExtraction.Incidence O N) (u : P → O)
    (active : P → Bool) (slot : P → PartnerProjection.Slot) (embed : R → P)
    (x : PartnerProjection.SourcePoint (fun j => g.rhs (u j)))
    (y : PartnerProjection.PartnerPoint (fun j => g.rhs (u j)) active)
    (hinside : ∀ r, active (embed r) = true)
    (hone : x.homogeneous = true)
    (hproject : PartnerProjection.project (fun j => g.rhs (u j)) active slot x = y) :
    ∀ r, g.namedAccepts (u (embed r))
      (g.name (u (embed r)) (slotIndex (slot (embed r))))
      (tripleCoordinates (x.coordinates (embed r))) (y.single (embed r)) := by
  exact IncidenceExtraction.augmented_accepts_implies_named_repeated_accepts g u
    (fun j => active j = true) (fun j => slotIndex (slot j)) embed
    (fullPoint x) (partnerPoint y) hinside
    (actual_projection_accepts g u active slot x y hone hproject)

end MaxCutGames.Soundness.ConcreteExtraction

namespace MaxCutGames.Reduction.ActualHomogeneous

open Integration.BinaryLinear
open scoped BigOperators

variable {k : Nat}

abbrev E (k : Nat) := F2 × (Fin k → F2 × F2)
abbrev Ambient (k : Nat) := F2 × (Fin k → Fin 3 → F2)

def tau : E k →ₗ[F2] F2 := LinearMap.fst F2 _ _
def hBasis (k : Nat) : E k := (1, 0)
def firstBasis (j : Fin k) : E k := (0, Pi.single j (1, 0))
def secondBasis (j : Fin k) : E k := (0, Pi.single j (0, 1))
def coordinateBasis (j : Fin k) (i : Fin 2) : E k :=
  if i = 0 then firstBasis j else secondBasis j

@[simp] theorem tau_hBasis : tau (hBasis k) = 1 := rfl
@[simp] theorem tau_firstBasis (j : Fin k) : tau (firstBasis j) = 0 := rfl
@[simp] theorem tau_secondBasis (j : Fin k) : tau (secondBasis j) = 0 := rfl

theorem pair_fst_ite (p : Prop) [Decidable p] (a b : F2 × F2) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split_ifs <;> rfl
theorem pair_snd_ite (p : Prop) [Decidable p] (a b : F2 × F2) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split_ifs <;> rfl

theorem coordinate_decomposition (x : E k) :
    x = x.1 • hBasis k + ∑ j : Fin k,
      ((x.2 j).1 • firstBasis j + (x.2 j).2 • secondBasis j) := by
  apply Prod.ext
  · simp [hBasis, firstBasis, secondBasis, Prod.fst_sum]
  · funext j
    apply Prod.ext <;>
      simp [hBasis, firstBasis, secondBasis, Pi.single_apply,
        Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, pair_fst_ite, pair_snd_ite]

theorem linearMap_expansion {R : Type*} [AddCommGroup R] [Module F2 R]
    (X : E k →ₗ[F2] R) (x : E k) :
    X x = x.1 • X (hBasis k) + ∑ j : Fin k,
      ((x.2 j).1 • X (firstBasis j) + (x.2 j).2 • X (secondBasis j)) := by
  conv_lhs => rw [coordinate_decomposition x]
  simp

def homogeneous (b : Fin k → F2) : Submodule F2 (Ambient k) where
  carrier := {x | ∀ j, x.2 j 0 + x.2 j 1 + x.2 j 2 = b j * x.1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j
    change (x.2 j 0 + y.2 j 0) + (x.2 j 1 + y.2 j 1) +
      (x.2 j 2 + y.2 j 2) = b j * (x.1 + y.1)
    calc
      _ = (x.2 j 0 + x.2 j 1 + x.2 j 2) +
          (y.2 j 0 + y.2 j 1 + y.2 j 2) := by ring
      _ = b j * x.1 + b j * y.1 := by rw [hx j, hy j]
      _ = _ := by ring
  smul_mem' := by
    intro c x hx j
    change c * x.2 j 0 + c * x.2 j 1 + c * x.2 j 2 = b j * (c * x.1)
    calc
      _ = c * (x.2 j 0 + x.2 j 1 + x.2 j 2) := by ring
      _ = c * (b j * x.1) := by rw [hx j]
      _ = _ := by ring

def embed (b : Fin k → F2) : E k →ₗ[F2] Ambient k where
  toFun x := (x.1, fun j => ![(x.2 j).1, (x.2 j).2,
    b j * x.1 + (x.2 j).1 + (x.2 j).2])
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext j i
      fin_cases i <;> simp ; ring
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · funext j i
      fin_cases i <;> simp [smul_eq_mul] ; ring

theorem embed_mem (b : Fin k → F2) (x : E k) : embed b x ∈ homogeneous b := by
  intro j
  change (x.2 j).1 + (x.2 j).2 + (b j * x.1 + (x.2 j).1 + (x.2 j).2) = b j * x.1
  have h1 := CharTwo.add_self_eq_zero ((x.2 j).1)
  have h2 := CharTwo.add_self_eq_zero ((x.2 j).2)
  calc
    _ = b j * x.1 + (((x.2 j).1 + (x.2 j).1) + ((x.2 j).2 + (x.2 j).2)) := by ring
    _ = _ := by rw [h1, h2]; simp

def equivalence (b : Fin k → F2) : E k ≃ₗ[F2] homogeneous b where
  toFun x := ⟨embed b x, embed_mem b x⟩
  invFun x := (x.1.1, fun j => (x.1.2 j 0, x.1.2 j 1))
  left_inv x := by rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext j i
      fin_cases i
      · rfl
      · rfl
      · change b j * x.1.1 + x.1.2 j 0 + x.1.2 j 1 = x.1.2 j 2
        rw [← x.property j]
        have h1 := CharTwo.add_self_eq_zero (x.1.2 j 0)
        have h2 := CharTwo.add_self_eq_zero (x.1.2 j 1)
        calc
          _ = x.1.2 j 2 + ((x.1.2 j 0 + x.1.2 j 0) + (x.1.2 j 1 + x.1.2 j 1)) := by ring
          _ = _ := by rw [h1, h2]; simp
  map_add' x y := Subtype.ext ((embed b).map_add x y)
  map_smul' c x := Subtype.ext ((embed b).map_smul c x)

theorem finrank_E (k : Nat) : Module.finrank F2 (E k) = 1 + 2 * k := by
  simp [E, Module.finrank_prod, Module.finrank_pi_fintype, Nat.mul_comm]

theorem finrank_homogeneous (b : Fin k → F2) :
    Module.finrank F2 (homogeneous b) = 1 + 2 * k := by
  rw [← (equivalence b).finrank_eq, finrank_E]

end MaxCutGames.Reduction.ActualHomogeneous

namespace MaxCutGames.Reduction.ActualCanonical

open Integration.BinaryLinear ActualHomogeneous
open scoped BigOperators

universe u v w
variable {k : Nat}
variable {Name : Type u} {Id : Type v} {R : Type w}
variable [AddCommGroup R] [Module F2 R] [DecidableEq R]

inductive Record (Name : Type u) (Id : Type v) (R : Type w)
  | blank
  | single (name : Name) (coefficient : R)
  | full (occurrence : Id) (coefficients : Fin 3 → R)
  deriving DecidableEq

def recordEquiv : Record Name Id R ≃ Unit ⊕ ((Name × R) ⊕ (Id × (Fin 3 → R))) where
  toFun r := match r with
    | .blank => .inl ()
    | .single n c => .inr (.inl (n,c))
    | .full e a => .inr (.inr (e,a))
  invFun r := match r with
    | .inl _ => .blank
    | .inr (.inl (n,c)) => .single n c
    | .inr (.inr (e,a)) => .full e a
  left_inv r := by cases r <;> rfl
  right_inv r := by rcases r with u | (p | p) <;> cases ‹_› <;> rfl

noncomputable instance [Fintype Name] [Fintype Id] [Fintype R] :
    Fintype (Record Name Id R) := Fintype.ofEquiv _ recordEquiv.symm

abbrev Data (k : Nat) (Name : Type u) (Id : Type v) (R : Type w) :=
  R × (Fin k → Record Name Id R)

def pivot (a : Fin 3 → R) : R :=
  if a 0 = a 1 then a 0 else if a 0 = a 2 then a 0 else a 2

def translate (a : Fin 3 → R) (t : R) : Fin 3 → R := fun i => a i + t
def normalize (a : Fin 3 → R) : Fin 3 → R := translate a (pivot a)

def record (names : Id → Fin 3 → Name) (e : Id) (a : Fin 3 → R) :
    Record Name Id R :=
  if a 0 = a 1 then
      if a 0 = a 2 then .blank else .single (names e 2) (a 2 + a 0)
    else if a 0 = a 2 then .single (names e 1) (a 1 + a 0)
    else if a 1 = a 2 then .single (names e 0) (a 0 + a 2)
    else .full e (normalize a)

def data (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (z : R) (a : Fin k → Fin 3 → R) : Data k Name Id R :=
  (z + ∑ j, rhs (occ j) • pivot (a j), fun j => record names (occ j) (a j))

def standardTriple (X : E k →ₗ[F2] R) (j : Fin k) : Fin 3 → R :=
  ![X (firstBasis j), X (secondBasis j), 0]

def canonical (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (X : E k →ₗ[F2] R) : Data k Name Id R :=
  data occ names rhs (X (hBasis k)) (standardTriple X)

def ambientEval (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R) (x : E k) : R :=
  x.1 • z + ∑ j, ((x.2 j).1 • a j 0 + (x.2 j).2 • a j 1 +
    (b j * x.1 + (x.2 j).1 + (x.2 j).2) • a j 2)

def Represents (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R)
    (X : E k →ₗ[F2] R) : Prop := ∀ x, ambientEval b z a x = X x

omit [DecidableEq R] in
theorem add_self (x : R) : x + x = 0 := by
  calc
    x + x = (1 + 1 : F2) • x := by simp [add_smul]
    _ = 0 := by rw [show (1 + 1 : F2) = 0 by decide, zero_smul]

omit [DecidableEq R] in
theorem add_both (x y t : R) : (x + t) + (y + t) = x + y := by
  calc
    _ = (x + y) + (t + t) := by abel
    _ = _ := by rw [add_self, add_zero]

omit [Module F2 R] in
theorem pivot_translate (a : Fin 3 → R) (t : R) :
    pivot (translate a t) = pivot a + t := by
  classical
  by_cases h1 : a 0 = a 1 <;> by_cases h2 : a 0 = a 2 <;>
    simp [pivot, translate, h1, h2]

theorem normalize_translate (a : Fin 3 → R) (t : R) :
    normalize (translate a t) = normalize a := by
  unfold normalize
  rw [pivot_translate]
  funext i
  exact add_both _ _ _

theorem record_translate (names : Id → Fin 3 → Name) (e : Id) (a : Fin 3 → R) (t : R) :
    record names e (translate a t) = record names e a := by
  classical
  have hs (i : Fin 3) : translate a t i = a i + t := rfl
  simp only [record, hs, add_right_cancel_iff, add_both, normalize_translate]

theorem data_gauge (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (z : R) (a : Fin k → Fin 3 → R) (t : Fin k → R) :
    data occ names rhs (z + ∑ j, rhs (occ j) • t j) (fun j => translate (a j) (t j)) =
      data occ names rhs z a := by
  apply Prod.ext
  · simp only [data, pivot_translate, smul_add, Finset.sum_add_distrib]
    exact add_both _ _ _
  · funext j
    exact record_translate names (occ j) (a j) (t j)

theorem data_global_shift (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (z c : R) (a : Fin k → Fin 3 → R) :
    data occ names rhs (z + c) a =
      ((data occ names rhs z a).1 + c, (data occ names rhs z a).2) := by
  apply Prod.ext
  · dsimp [data]; abel
  · rfl

theorem canonical_shift (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (X : E k →ₗ[F2] R) (c : R) :
    canonical occ names rhs (X + tau.smulRight c) =
      ((canonical occ names rhs X).1 + c, (canonical occ names rhs X).2) := by
  have ht : standardTriple (X + tau.smulRight c) = standardTriple X := by
    funext j i
    fin_cases i <;> simp [standardTriple, tau, firstBasis, secondBasis]
  simp only [canonical, ht]
  have hg : (X + tau.smulRight c : E k →ₗ[F2] R) (hBasis k) = X (hBasis k) + c := by
    simp [hBasis, tau]
  rw [hg]
  exact data_global_shift occ names rhs _ c _

omit [DecidableEq R] in
@[simp] theorem ambientEval_hBasis (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R) :
    ambientEval b z a (hBasis k) = z + ∑ j, b j • a j 2 := by
  simp [ambientEval, hBasis]

omit [DecidableEq R] in
@[simp] theorem ambientEval_firstBasis (b : Fin k → F2) (z : R)
    (a : Fin k → Fin 3 → R) (j : Fin k) :
    ambientEval b z a (firstBasis j) = a j 0 + a j 2 := by
  classical
  simp only [ambientEval, firstBasis, zero_smul, zero_add, mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

omit [DecidableEq R] in
@[simp] theorem ambientEval_secondBasis (b : Fin k → F2) (z : R)
    (a : Fin k → Fin 3 → R) (j : Fin k) :
    ambientEval b z a (secondBasis j) = a j 1 + a j 2 := by
  classical
  simp only [ambientEval, secondBasis, zero_smul, zero_add, mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

omit [DecidableEq R] in
/-- Every actual linear map has the claimed ambient coefficient extension. -/
theorem standard_represents (b : Fin k → F2) (X : E k →ₗ[F2] R) :
    Represents b (X (hBasis k)) (standardTriple X) X := by
  intro x
  simpa [ambientEval, standardTriple] using (linearMap_expansion X x).symm

omit [DecidableEq R] in
/-- Equality on the homogeneous space forces the free-coordinate identities. -/
theorem extension_coefficients (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R)
    (X : E k →ₗ[F2] R) (h : Represents b z a X) :
    X (hBasis k) = z + ∑ j, b j • a j 2 ∧
      ∀ j, X (firstBasis j) = a j 0 + a j 2 ∧
        X (secondBasis j) = a j 1 + a j 2 := by
  constructor
  · simpa only [ambientEval_hBasis] using (h (hBasis k)).symm
  · intro j
    exact ⟨by simpa only [ambientEval_firstBasis] using (h (firstBasis j)).symm,
      by simpa only [ambientEval_secondBasis] using (h (secondBasis j)).symm⟩

/-- Every ambient extension of a genuine map gives the same canonical data. -/
theorem canonical_eq_of_extension (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (z : R) (a : Fin k → Fin 3 → R) (X : E k →ₗ[F2] R)
    (h : Represents (fun j => rhs (occ j)) z a X) :
    canonical occ names rhs X = data occ names rhs z a := by
  obtain ⟨hz, ha⟩ := extension_coefficients _ z a X h
  have ht : standardTriple X = fun j => translate (a j) (a j 2) := by
    funext j i
    fin_cases i
    · exact (ha j).1
    · exact (ha j).2
    · exact (add_self (a j 2)).symm
  unfold canonical
  rw [hz, ht]
  exact data_gauge occ names rhs z a (fun j => a j 2)

theorem extension_independent (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (z z' : R) (a a' : Fin k → Fin 3 → R) (X : E k →ₗ[F2] R)
    (h : Represents (fun j => rhs (occ j)) z a X)
    (h' : Represents (fun j => rhs (occ j)) z' a' X) :
    data occ names rhs z a = data occ names rhs z' a' :=
  (canonical_eq_of_extension occ names rhs z a X h).symm.trans
    (canonical_eq_of_extension occ names rhs z' a' X h')

def singletonTriple (i : Fin 3) (c : R) : Fin 3 → R := Pi.single i c

omit [Module F2 R] in
theorem pivot_singleton (i : Fin 3) (c : R) : pivot (singletonTriple i c) = 0 := by
  classical
  by_cases hc : c = 0 <;> fin_cases i <;> simp [singletonTriple, pivot, hc]

omit [Module F2 R] in
theorem record_singleton (names : Id → Fin 3 → Name) (e : Id) (i : Fin 3) (c : R) :
    record names e (singletonTriple i c) =
      (if c = 0 then Record.blank else Record.single (names e i) c) := by
  classical
  by_cases hc : c = 0 <;> fin_cases i <;>
    simp [record, singletonTriple, hc, eq_comm]

theorem singleton_global_adjustment (rhs : Id → F2) (e : Id) (i : Fin 3) (c : R) :
    rhs e • pivot (singletonTriple i c) = 0 := by rw [pivot_singleton, smul_zero]

omit [Module F2 R] in
/-- The hidden occurrence and its internal slot cannot affect a retained
single-variable record. The occurrence need not differ from other positions. -/
theorem singleton_locality (names : Id → Fin 3 → Name) (e e' : Id)
    (i i' : Fin 3) (c : R) (hname : names e i = names e' i') :
    record names e (singletonTriple i c) = record names e' (singletonTriple i' c) := by
  simp only [record_singleton, hname]

end MaxCutGames.Reduction.ActualCanonical

/-! Canonical-row descent for every actual partner linear map. -/

namespace MaxCutGames.Soundness.ActualCanonicalPullback

open scoped BigOperators
open PartnerProjection PartnerMapCoordinates
open ConditionalIncidences
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction

noncomputable section

variable {k : Nat} (rhsB : Fin k → Bool) (J : Finset (Fin k))
variable (R : Type) [AddCommGroup R] [Module F2 R]

def selectedFree (b : Fin k → F2) (slot : Fin k → Slot)
    (v : ActualHomogeneous.E k) (j : Fin k) : F2 :=
  match slot j with
  | .first => (v.2 j).1
  | .second => (v.2 j).2
  | .third => b j * v.1 + (v.2 j).1 + (v.2 j).2

def ambientCoefficients (gamma : RawCoefficients J R) (slot : Fin k → Slot)
    (j : Fin k) (i : Fin 3) : R :=
  if hj : j ∈ J then
    if i = ConcreteExtraction.slotIndex (slot j) then gamma (some (.inr ⟨j,hj⟩)) else 0
  else if i = 0 then gamma (some (.inl (⟨j,hj⟩,0)))
    else if i = 1 then gamma (some (.inl (⟨j,hj⟩,1))) else 0

def freePullback (gamma : RawCoefficients J R) (slot : Fin k → Slot) :
    ActualHomogeneous.E k →ₗ[F2] R :=
  (mapEquiv rhsB J R gamma).comp
    ((PartnerLinear.projection rhsB (activeOf J) slot).comp
      (PartnerLinear.sourceLinearEquiv rhsB).symm.toLinearMap)

theorem ofBit_and (a b : Bool) : ofBit (a && b) = ofBit a * ofBit b := by
  cases a <;> cases b <;> decide

theorem inverse_homogeneous (v : ActualHomogeneous.E k) :
    ofBit (((PartnerLinear.sourceLinearEquiv rhsB).symm v).homogeneous) = v.1 :=
  ofBit_toBit _

theorem inverse_first (v : ActualHomogeneous.E k) (j : Fin k) :
    ofBit ((((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j).first) =
      (v.2 j).1 := ofBit_toBit _

theorem inverse_second (v : ActualHomogeneous.E k) (j : Fin k) :
    ofBit ((((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j).second) =
      (v.2 j).2 := ofBit_toBit _

theorem inverse_retained_free (v : ActualHomogeneous.E k) (j : Fin k)
    (slot : Fin k → Slot) :
    ofBit (retained (slot j)
      (((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j)) =
        selectedFree (fun j => ofBit (rhsB j)) slot v j := by
  unfold selectedFree
  cases hslot : slot j with
  | first => exact ofBit_toBit _
  | second => exact ofBit_toBit _
  | third =>
    change ofBit (((rhsB j && toBit v.1).xor (toBit (v.2 j).1)).xor
      (toBit (v.2 j).2)) = ofBit (rhsB j) * v.1 + (v.2 j).1 + (v.2 j).2
    rw [ofBit_xor, ofBit_xor, ofBit_and, ofBit_toBit, ofBit_toBit, ofBit_toBit]

theorem freePullback_expansion (gamma : RawCoefficients J R)
    (slot : Fin k → Slot) (v : ActualHomogeneous.E k) :
    freePullback rhsB J R gamma slot v =
      v.1 • gamma none +
        (∑ j : PositionOutside J, ((v.2 j.val).1 • gamma (some (.inl (j,0))) +
          (v.2 j.val).2 • gamma (some (.inl (j,1))))) +
        ∑ j : PositionInside J, selectedFree (fun j => ofBit (rhsB j)) slot v j.val •
          gamma (some (.inr j)) := by
  change mapEquiv rhsB J R gamma
    (PartnerLinear.projection rhsB (activeOf J) slot
      ((PartnerLinear.sourceLinearEquiv rhsB).symm v)) = _
  rw [pullback_expansion]
  simp only [inverse_homogeneous, inverse_first, inverse_second, inverse_retained_free]

def outsideInsideEquiv : (PositionOutside J ⊕ PositionInside J) ≃ Fin k where
  toFun j := Sum.elim Subtype.val Subtype.val j
  invFun j := if hj : j ∈ J then Sum.inr ⟨j,hj⟩ else Sum.inl ⟨j,hj⟩
  left_inv j := by
    cases j with
    | inl j => simp [j.property]
    | inr j => simp [j.property]
  right_inv j := by
    by_cases hj : j ∈ J <;> simp [hj]

omit [Module F2 R] in
theorem sum_outside_inside (f : PositionOutside J → R) (g : PositionInside J → R) :
    (∑ j, f j) + (∑ j, g j) =
      ∑ j : Fin k, if hj : j ∈ J then g ⟨j,hj⟩ else f ⟨j,hj⟩ := by
  rw [← (outsideInsideEquiv J).sum_comp]
  rw [Fintype.sum_sum_type]
  congr 1 <;> apply Finset.sum_congr rfl
  · intro j _
    simp [outsideInsideEquiv, j.property]
  · intro j _
    simp [outsideInsideEquiv, j.property]

theorem raw_represents (gamma : RawCoefficients J R) (slot : Fin k → Slot) :
    ActualCanonical.Represents (fun j => ofBit (rhsB j)) (gamma none)
      (ambientCoefficients J R gamma slot) (freePullback rhsB J R gamma slot) := by
  intro v
  let f : PositionOutside J → R := fun j =>
    (v.2 j.val).1 • gamma (some (.inl (j,0))) +
      (v.2 j.val).2 • gamma (some (.inl (j,1)))
  let g : PositionInside J → R := fun j =>
    selectedFree (fun j => ofBit (rhsB j)) slot v j.val • gamma (some (.inr j))
  have hs : (∑ j, f j) + (∑ j, g j) =
      ∑ j : Fin k, ((v.2 j).1 • ambientCoefficients J R gamma slot j 0 +
        (v.2 j).2 • ambientCoefficients J R gamma slot j 1 +
        (ofBit (rhsB j) * v.1 + (v.2 j).1 + (v.2 j).2) •
          ambientCoefficients J R gamma slot j 2) := by
    rw [sum_outside_inside]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · cases hslot : slot j <;>
        simp [g, ambientCoefficients, selectedFree, hj, hslot, ConcreteExtraction.slotIndex]
    · simp [f, ambientCoefficients, hj]
  calc
    ActualCanonical.ambientEval _ _ _ v = v.1 • gamma none + ((∑ j, f j) + (∑ j, g j)) :=
      congrArg (fun z : R => v.1 • gamma none + z) hs.symm
    _ = (v.1 • gamma none + (∑ j, f j)) + (∑ j, g j) := (add_assoc _ _ _).symm
    _ = freePullback rhsB J R gamma slot v :=
      (freePullback_expansion rhsB J R gamma slot v).symm

theorem canonical_raw_pullback [DecidableEq R] {Id Name : Type} [DecidableEq Id] [DecidableEq Name]
    (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (gamma : RawCoefficients J R) (slot : Fin k → Slot) :
    ActualCanonical.canonical occ names rhs
      (freePullback (fun j => toBit (rhs (occ j))) J R gamma slot) =
    ActualCanonical.data occ names rhs (gamma none) (ambientCoefficients J R gamma slot) := by
  apply ActualCanonical.canonical_eq_of_extension
  simpa only [ofBit_toBit] using raw_represents (fun j => toBit (rhs (occ j))) J R gamma slot

omit [Module F2 R] in
theorem ambientCoefficients_single (gamma : RawCoefficients J R) (slot : Fin k → Slot)
    (j : Fin k) (hj : j ∈ J) :
    ambientCoefficients J R gamma slot j =
      ActualCanonical.singletonTriple (ConcreteExtraction.slotIndex (slot j))
        (gamma (some (.inr ⟨j,hj⟩))) := by
  funext i
  simp [ambientCoefficients, hj, ActualCanonical.singletonTriple, Pi.single_apply]

omit [Module F2 R] in
theorem ambientCoefficients_full_eq (gamma : RawCoefficients J R)
    (slot slot' : Fin k → Slot) (j : Fin k) (hj : j ∉ J) :
    ambientCoefficients J R gamma slot j = ambientCoefficients J R gamma slot' j := by
  funext i
  simp [ambientCoefficients, hj]

/-- Raw canonical data is determined by the full displayed occurrences and
    retained variable names. Hidden single occurrences and slot indices vanish. -/
theorem raw_data_locality [DecidableEq R] {Id Name : Type}
    (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot)
    (gamma : RawCoefficients J R)
    (hfull : ∀ j, j ∉ J → occ j = occ' j)
    (hsingle : ∀ j, j ∈ J → names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
      names (occ' j) (ConcreteExtraction.slotIndex (slot' j))) :
    ActualCanonical.data occ names rhs (gamma none) (ambientCoefficients J R gamma slot) =
      ActualCanonical.data occ' names rhs (gamma none) (ambientCoefficients J R gamma slot') := by
  apply Prod.ext
  · change gamma none + _ = gamma none + _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · rw [ambientCoefficients_single J R gamma slot j hj,
        ambientCoefficients_single J R gamma slot' j hj]
      simp only [ActualCanonical.singleton_global_adjustment]
    · rw [hfull j hj, ambientCoefficients_full_eq J R gamma slot slot' j hj]
  · funext j
    change ActualCanonical.record names (occ j) (ambientCoefficients J R gamma slot j) =
      ActualCanonical.record names (occ' j) (ambientCoefficients J R gamma slot' j)
    by_cases hj : j ∈ J
    · rw [ambientCoefficients_single J R gamma slot j hj,
        ambientCoefficients_single J R gamma slot' j hj]
      exact ActualCanonical.singleton_locality names _ _ _ _ _ (hsingle j hj)
    · rw [hfull j hj, ambientCoefficients_full_eq J R gamma slot slot' j hj]

/-- Lemma 6.2 for the actual pullbacks in the shared F₂ coordinate model. -/
theorem canonical_private_input_locality [DecidableEq R]
    {Id Name : Type} [DecidableEq Id] [DecidableEq Name]
    (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot)
    (gamma : RawCoefficients J R)
    (hfull : ∀ j, j ∉ J → occ j = occ' j)
    (hsingle : ∀ j, j ∈ J → names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
      names (occ' j) (ConcreteExtraction.slotIndex (slot' j))) :
    ActualCanonical.canonical occ names rhs
      (freePullback (fun j => toBit (rhs (occ j))) J R gamma slot) =
    ActualCanonical.canonical occ' names rhs
      (freePullback (fun j => toBit (rhs (occ' j))) J R gamma slot') := by
  rw [canonical_raw_pullback, canonical_raw_pullback]
  exact raw_data_locality J R names rhs occ occ' slot slot' gamma hfull hsingle

end
end MaxCutGames.Soundness.ActualCanonicalPullback

end OAI
