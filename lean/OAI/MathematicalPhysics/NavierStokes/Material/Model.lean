import Mathlib

namespace OAI

namespace Alternating

open scoped BigOperators
open MeasureTheory

abbrev Instruction := ℕ × ℕ × Fin 3

abbrev Machine := ℕ × ℕ × Finset ℕ × List (List (Option Instruction))

abbrev MachineInput := Machine × List ℕ

def Machine.stateCount (M : Machine) : ℕ := M.1 + 1

def Machine.symbolCount (M : Machine) : ℕ := M.2.1 + 1

def Machine.haltingStates (M : Machine) : Finset ℕ := M.2.2.1

def Machine.table (M : Machine) : List (List (Option Instruction)) := M.2.2.2

def Machine.WellFormed (M : Machine) : Prop :=
  M.table.length = M.stateCount ∧
  (∀ q ∈ M.haltingStates, q < M.stateCount) ∧
  ∀ row ∈ M.table,
    row.length = M.symbolCount ∧
    ∀ i : Instruction, some i ∈ row →
      i.1 < M.stateCount ∧ i.2.1 < M.symbolCount

def ValidInput (I : MachineInput) : Prop :=
  I.1.WellFormed ∧ ∀ a ∈ I.2, a < I.1.symbolCount

theorem ValidInput.machine_wellFormed {I : MachineInput} (hI : ValidInput I) :
    I.1.WellFormed := hI.1

structure Configuration where
  state : ℕ
  head : ℤ
  tape : ℤ → ℕ

def Machine.isHalting (M : Machine) (q : ℕ) : Bool :=
  decide (q = M.stateCount ∨ q ∈ M.haltingStates)

def Machine.instruction (M : Machine) (q a : ℕ) : Option Instruction :=
  ((M.table[q]?).bind fun row => row[a]?).join

def Machine.step (M : Machine) (c : Configuration) : Configuration :=
  if M.isHalting c.state then c
  else match M.instruction c.state (c.tape c.head) with
    | none => { c with state := M.stateCount }
    | some i =>
      { state := i.1
        head := c.head + (i.2.2.val : ℤ) - 1
        tape := Function.update c.tape c.head i.2.1 }

def initialConfiguration (w : List ℕ) : Configuration :=
  { state := 0
    head := 0
    tape := fun j => if j < 0 then 0 else (w[j.toNat]?).getD 0 }

def configurationAt (I : MachineInput) (n : ℕ) : Configuration :=
  I.1.step^[n] (initialConfiguration I.2)

def Halts (I : MachineInput) : Prop :=
  ∃ n : ℕ, I.1.isHalting (configurationAt I n).state = true

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Field := ℝ → Space → Space
abbrev Pressure := ℝ → Space → ℝ
abbrev MultiIndex := Fin 3 → ℕ

noncomputable section

def basisVector (i : Fin 3) : Space := EuclideanSpace.single i 1

def multiOrder (α : MultiIndex) : ℕ := ∑ i, α i

def spatialD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (g : Space → E) : Space → E :=
  fun x => fderiv ℝ g x (basisVector i)

def spatialPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : MultiIndex) (g : Space → E) : Space → E :=
  (spatialD 2)^[α 2] ((spatialD 1)^[α 1] ((spatialD 0)^[α 0] g))

def timeD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) : ℝ → E := fun t => derivWithin g (Set.Ici 0) t

def mixedPartial (u : Field) (l : ℕ) (α : MultiIndex) (t : ℝ) (x : Space) : Space :=
  timeD^[l] (fun s => spatialPartial α (u s) x) t

def timeDerivative (u : Field) (t : ℝ) (x : Space) : Space :=
  timeD (fun s => u s x) t

def divergence (u : Space → Space) (x : Space) : ℝ :=
  ∑ i : Fin 3, spatialD i u x i

def gradient (p : Space → ℝ) (x : Space) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => spatialD i p x)

def laplacian (u : Space → Space) (x : Space) : Space :=
  ∑ i : Fin 3, spatialD i (spatialD i u) x

def convection (u : Space → Space) (x : Space) : Space :=
  ∑ i : Fin 3, (u x i) • spatialD i u x

def residual (ν : ℝ) (u : Field) : Field :=
  fun t x => timeDerivative u t x + convection (u t) x - ν • laplacian (u t) x

def timeSpace : Set (ℝ × Space) := Set.Ici 0 ×ˢ Set.univ

def SmoothUpToZero (u : Field) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) timeSpace

def SupportedIn (K : Set Space) (u : Field) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x : Space, x ∉ K → u t x = 0

def RapidDecay (u : Field) : Prop :=
  ∀ (J l : ℕ) (α : MultiIndex), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t : ℝ), 0 ≤ t → ∀ x : Space,
      (1 + t + ‖x‖) ^ J * ‖mixedPartial u l α t x‖ ≤ C

def ClassicalRegularity (u : Field) (p : Pressure) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ContDiff ℝ 2 (u t) ∧ ContDiff ℝ 1 (p t)) ∧
  (∀ x : Space, DifferentiableOn ℝ (fun t => u t x) (Set.Ici 0)) ∧
  ∀ T : ℝ, 0 ≤ T →
    ContinuousOn (Function.uncurry (timeDerivative u)) (Set.Icc 0 T ×ˢ Set.univ) ∧
    (∀ α : MultiIndex, multiOrder α ≤ 2 →
      ContinuousOn (fun tx : ℝ × Space => spatialPartial α (u tx.1) tx.2)
        (Set.Icc 0 T ×ˢ Set.univ)) ∧
    (∀ α : MultiIndex, multiOrder α ≤ 1 →
      ContinuousOn (fun tx : ℝ × Space => spatialPartial α (p tx.1) tx.2)
        (Set.Icc 0 T ×ˢ Set.univ))

def NSSolution (ν : ℝ) (f u : Field) (p : Pressure) : Prop :=
  ClassicalRegularity u p ∧
  (∀ x : Space, u 0 x = 0) ∧
  ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
    divergence (u t) x = 0 ∧
    timeDerivative u t x + convection (u t) x =
      -gradient (p t) x + ν • laplacian (u t) x + f t x

abbrev SpatialL2 (E : Type*) [NormedAddCommGroup E] :=
  MeasureTheory.Lp E 2 (MeasureTheory.volume : MeasureTheory.Measure Space)

def ContinuousInSobolev {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (g : ℝ → Space → E) (T : ℝ) : Prop :=
  ∀ α : MultiIndex, multiOrder α ≤ k →
    ∃ G : ℝ → SpatialL2 E,
      ContinuousOn G (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        (fun x : Space => (G t) x) =ᵐ[volume] spatialPartial α (g t)

def C1InL2 (u : Field) (T : ℝ) : Prop :=
  ∃ U W : ℝ → SpatialL2 Space,
    ContinuousOn U (Set.Icc 0 T) ∧ ContinuousOn W (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ((fun x : Space => (U t) x) =ᵐ[volume] u t) ∧
      ((fun x : Space => (W t) x) =ᵐ[volume] timeDerivative u t) ∧
      HasDerivWithinAt U (W t) (Set.Icc 0 T) t

def EnergyClass (u : Field) (p : Pressure) : Prop :=
  ∀ T : ℝ, 0 ≤ T →
    ContinuousInSobolev 2 u T ∧ C1InL2 u T ∧ ContinuousInSobolev 1 p T ∧
    ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : Space,
      ‖u t x‖ + ‖fderiv ℝ (u t) x‖ ≤ C

def CompetitorEnergyClass (u : Field) (p : Pressure) : Prop :=
  ∀ T : ℝ, 0 ≤ T →
    ContinuousInSobolev 2 u T ∧ C1InL2 u T ∧ ContinuousInSobolev 1 p T ∧
    ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : Space, ‖u t x‖ ≤ C

def SolvesParticle (u : Field) (a : Space) (γ : ℝ → Space) : Prop :=
  γ 0 = a ∧ ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt γ (u t (γ t)) (Set.Ici 0) t

def GlobalMaterialFlow (u : Field) (X : ℝ → Space → Space) : Prop :=
  (∀ a : Space, SolvesParticle u a (fun t => X t a)) ∧
  ∀ (a : Space) (γ : ℝ → Space), SolvesParticle u a γ →
    ∀ t : ℝ, 0 ≤ t → γ t = X t a

def observedParticle : Space := -basisVector 0

abbrev Program := Nat.Partrec.Code
abbrev RationalPoint := ℚ × ℚ × ℚ

def rationalPoint (q : RationalPoint) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![(q.1 : ℝ), (q.2.1 : ℝ), (q.2.2 : ℝ)]

def error (k : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ k

def ComputableReal (x : ℝ) : Prop :=
  ∃ c : Program, ∀ k : ℕ, ∃ q : ℚ,
    Encodable.encode q ∈ c.eval k ∧ |x - (q : ℝ)| ≤ error k

abbrev FieldProgram := Program × Program × Program

def EvaluatesField (c : FieldProgram) (u : Field) : Prop :=
  (∀ (l : ℕ) (α : MultiIndex) (t : ℚ), 0 ≤ t →
    ∀ (x : RationalPoint) (k : ℕ), ∃ q : RationalPoint,
      Encodable.encode q ∈ c.1.eval (Encodable.encode (l, α, t, x, k)) ∧
      ‖mixedPartial u l α (t : ℝ) (rationalPoint x) - rationalPoint q‖ ≤ error k) ∧
  (∀ (l : ℕ) (α : MultiIndex) (k : ℕ), ∃ m : ℕ,
    m ∈ c.2.1.eval (Encodable.encode (l, α, k)) ∧
    ∀ (t s : ℝ), 0 ≤ t → 0 ≤ s → ∀ x y : Space,
      |t - s| + ‖x - y‖ ≤ error m →
      ‖mixedPartial u l α t x - mixedPartial u l α s y‖ ≤ error k) ∧
  (∀ (J l : ℕ) (α : MultiIndex), ∃ C : ℚ,
    Encodable.encode C ∈ c.2.2.eval (Encodable.encode (J, l, α)) ∧ 0 ≤ C ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      (1 + t + ‖x‖) ^ J * ‖mixedPartial u l α t x‖ ≤ (C : ℝ))

def AlternatingOutput (ν : ℝ) (K : Set Space) (I : MachineInput)
    (velocityProgram forceProgram : FieldProgram) : Prop :=
  ∃ (u f : Field) (X : ℝ → Space → Space),
    EvaluatesField velocityProgram u ∧ EvaluatesField forceProgram f ∧
    SmoothUpToZero u ∧ SmoothUpToZero f ∧
    SupportedIn K u ∧ SupportedIn K f ∧ RapidDecay u ∧ RapidDecay f ∧
    f = residual ν u ∧
    NSSolution ν f u (fun _ _ => 0) ∧ EnergyClass u (fun _ _ => 0) ∧
    (∀ (v : Field) (p : Pressure), NSSolution ν f v p → CompetitorEnergyClass v p →
      ∀ t : ℝ, 0 ≤ t → ∀ x : Space, v t x = u t x ∧ p t x = 0) ∧
    GlobalMaterialFlow u X ∧
    ((∃ t : ℝ, 0 ≤ t ∧ 0 < X t observedParticle 0) ↔ Halts I)

end

end Alternating

end OAI
