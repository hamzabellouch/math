import Mathlib

namespace OAI

namespace ThreeMachine

structure Instance (n : ℕ) where
  edges : List (Fin n × Fin n)

def Instance.edge {n : ℕ} (G : Instance n) (u v : Fin n) : Prop :=
  (u, v) ∈ G.edges

def Instance.acyclic {n : ℕ} (G : Instance n) : Prop :=
  ∀ v, ¬Relation.TransGen G.edge v v

def Feasible {n : ℕ} (G : Instance n) (T : ℕ) (τ : Fin n → ℕ) : Prop :=
  (∀ v, 1 ≤ τ v ∧ τ v ≤ T) ∧
  (∀ t, ((Finset.univ : Finset (Fin n)).filter (fun v => τ v = t)).card ≤ 3) ∧
  ∀ u v, G.edge u v → τ u < τ v

def encodeNat (n : ℕ) : List Bool :=
  let b := Computability.encodeNat n
  List.replicate b.length true ++ false :: b

def encodeList {α : Type} (f : α → List Bool) (xs : List α) : List Bool :=
  encodeNat xs.length ++ xs.flatMap f

def encodeInput {n : ℕ} (G : Instance n) (deadline : Option ℕ) : List Bool :=
  (match deadline with
    | none => [false]
    | some T => true :: encodeNat T) ++
  encodeList encodeNat ((List.range n).map (· + 1)) ++
  encodeList (fun (e : Fin n × Fin n) => encodeNat (e.1.val + 1) ++
    encodeNat (e.2.val + 1)) G.edges

def encodeAnswer : Option (List ℕ) → List Bool
  | none => [false]
  | some slots => true :: encodeList encodeNat slots

def slots {n : ℕ} (τ : Fin n → ℕ) : List ℕ := List.ofFn τ

def CorrectOutput {n : ℕ} (G : Instance n) (deadline : Option ℕ)
    (out : List Bool) : Prop :=
  match deadline with
  | none => ∃ T τ, Feasible G T τ ∧
      (∀ T' τ', Feasible G T' τ' → T ≤ T') ∧
      out = encodeAnswer (some (slots τ))
  | some T =>
      (out = encodeAnswer none ∧ ¬∃ τ, Feasible G T τ) ∨
      ∃ τ, Feasible G T τ ∧ out = encodeAnswer (some (slots τ))

structure Machine (k q g : ℕ) where
  transition : Fin (q + 1) → (Fin (k + 1) → Fin (g + 3)) →
    Option (Fin (q + 1) × (Fin (k + 1) → Fin (g + 3) × Option Turing.Dir))

structure Configuration (k q g : ℕ) where
  state : Fin (q + 1)
  tapes : Fin (k + 1) → Turing.Tape (Fin (g + 3))

def bitSymbol {g : ℕ} (b : Bool) : Fin (g + 3) :=
  if b then ⟨2, by omega⟩ else ⟨1, by omega⟩

def Machine.step {k q g : ℕ} (M : Machine k q g)
    (c : Configuration k q g) : Option (Configuration k q g) := do
  let (state, action) ← M.transition c.state (fun i => (c.tapes i).head)
  return { state := state, tapes := fun i =>
    let tape := (c.tapes i).write (action i).1
    match (action i).2 with
    | none => tape
    | some d => tape.move d }

def Machine.initial {k q g : ℕ} (_M : Machine k q g)
    (input : List Bool) : Configuration k q g :=
  { state := 0, tapes := fun i =>
      Turing.Tape.mk₁ (if i = 0 then input.map bitSymbol else []) }

def Machine.run {k q g : ℕ} (M : Machine k q g) (input : List Bool)
    (t : ℕ) : Configuration k q g :=
  (fun c => (M.step c).getD c)^[t] (M.initial input)

def Machine.Produces {k q g : ℕ} (M : Machine k q g)
    (input out : List Bool) (timeBound : ℕ) : Prop :=
  ∃ t ≤ timeBound, M.step (M.run input t) = none ∧
    ((M.run input t).tapes 0).right₀ = Turing.ListBlank.mk (out.map bitSymbol)

def ReleaseTheorem : Prop :=
  ∃ (k q g : ℕ) (M : Machine k q g) (C : ℕ), 0 < C ∧
    ∀ n (G : Instance n), 1 ≤ n → G.acyclic →
      ∀ deadline : Option ℕ,
        (∀ T ∈ deadline, 1 ≤ T ∧ T ≤ n) →
        ∃ out, CorrectOutput G deadline out ∧
          M.Produces (encodeInput G deadline) out
            (C * ((encodeInput G deadline).length + 2) ^ 150020)

end ThreeMachine

end OAI
