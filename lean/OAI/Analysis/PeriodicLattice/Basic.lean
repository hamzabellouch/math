import Mathlib

namespace OAI

/-! Finite machines, computable names, torus fields and the lattice conclusion. -/

namespace PeriodicLattice

theorem neZeroThree : NeZero 3 := ⟨Nat.succ_ne_zero 2⟩
theorem twoAtLeastTwo : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩
theorem threeAtLeastTwo : Nat.AtLeastTwo 3 := ⟨by decide⟩
theorem fourAtLeastTwo : Nat.AtLeastTwo 4 := ⟨by decide⟩
theorem eightAtLeastTwo : Nat.AtLeastTwo 8 := ⟨by decide⟩

local instance finiteFunctionEncodingBasic {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

structure Instruction where
  nextState : ℕ
  writeSymbol : ℕ
  move : Fin 3
  deriving DecidableEq

def Instruction.codeEquiv : Instruction ≃ ℕ × ℕ × Fin 3 where
  toFun I := (I.nextState, I.writeSymbol, I.move)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Instruction := Primcodable.ofEquiv _ Instruction.codeEquiv

structure Machine where
  states : ℕ
  symbols : ℕ
  start : ℕ
  table : List (List (Option Instruction))
  deriving DecidableEq

def Machine.codeEquiv : Machine ≃ ℕ × ℕ × ℕ × List (List (Option Instruction)) where
  toFun M := (M.states, M.symbols, M.start, M.table)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Machine := Primcodable.ofEquiv _ Machine.codeEquiv

def Machine.lookup (M : Machine) (q a : ℕ) : Option Instruction :=
  (M.table.getD q []).getD a none

def Machine.WellFormed (M : Machine) : Prop :=
  0 < M.states ∧ 0 < M.symbols ∧ M.start < M.states ∧
  M.table.length ≤ M.states ∧
  (∀ row ∈ M.table, row.length ≤ M.symbols) ∧
  ∀ row ∈ M.table, ∀ entry ∈ row, ∀ I, entry = some I →
    I.nextState < M.states ∧ I.writeSymbol < M.symbols

structure Input where
  machine : Machine
  word : List ℕ
  deriving DecidableEq

def Input.codeEquiv : Input ≃ Machine × List ℕ where
  toFun d := (d.machine, d.word)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Input := Primcodable.ofEquiv _ Input.codeEquiv

def Input.WellFormed (d : Input) : Prop :=
  d.machine.WellFormed ∧ ∀ a ∈ d.word, a < d.machine.symbols

structure Configuration where
  state : ℕ
  head : ℤ
  tape : ℤ → ℕ

def initialConfiguration (d : Input) : Configuration where
  state := d.machine.start
  head := 0
  tape i := if 0 ≤ i then d.word.getD i.toNat 0 else 0

def machineStep (M : Machine) (c : Configuration) : Configuration :=
  match M.lookup c.state (c.tape c.head) with
  | none => c
  | some I =>
    { state := I.nextState
      head := c.head + ((I.move.val : ℤ) - 1)
      tape := Function.update c.tape c.head I.writeSymbol }

def execution (d : Input) (n : ℕ) : Configuration :=
  (machineStep d.machine)^[n] (initialConfiguration d)

def Halts (d : Input) : Prop :=
  ∃ n : ℕ, d.machine.lookup (execution d n).state
    ((execution d n).tape (execution d n).head) = none

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Torus := UnitAddTorus (Fin 3)
abbrev Field (A : Type*) := ℝ → Torus → A
abbrev VectorField := Field Space
abbrev ScalarField := Field ℝ
abbrev MultiIndex := Fin 3 → ℕ

noncomputable section

def torusMk (x : Space) : Torus := fun i => (x i : UnitAddCircle)

def torusVolume : MeasureTheory.Measure Torus :=
  MeasureTheory.Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle)

def initialParticle : Space := WithLp.toLp 2 ![(1 : ℝ) / 4, 1 / 2, 1 / 2]

def detector : Set Torus :=
  {q | ∃ s : ℝ, 1 / 2 < s ∧ s < 1 ∧ (s : UnitAddCircle) = q 0}

section Operators
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

def lifted (F : Field A) : ℝ × Space → A :=
  fun tx => F tx.1 (torusMk tx.2)

def spaceLift (F : Field A) (t : ℝ) : Space → A :=
  fun x => F t (torusMk x)

def Smooth (F : Field A) : Prop :=
  ContDiffOn ℝ (↑(⊤ : ℕ∞)) (lifted F) (Set.Ici (0 : ℝ) ×ˢ Set.univ)

def timeD (F : Field A) : Field A :=
  fun t q => derivWithin (fun s => F s q) (Set.Ici (0 : ℝ)) t

def spaceD (i : Fin 3) (F : Field A) : Field A :=
  fun t q => deriv (fun s : ℝ =>
    F t (q + torusMk (EuclideanSpace.single i s))) 0

def mixedD (r : ℕ) (α : MultiIndex) (F : Field A) : Field A :=
  timeD^[r] ((spaceD 2)^[α 2] ((spaceD 1)^[α 1] ((spaceD 0)^[α 0] F)))

def laplacian (F : Field A) : Field A :=
  fun t q => ∑ i : Fin 3, spaceD i (spaceD i F) t q

def MeanZero (F : Field A) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∫ q, F t q ∂torusVolume = 0

def spatialSup (F : Field A) (t : ℝ) : ℝ :=
  sSup (Set.range fun q => ‖F t q‖)

def CylinderContinuous (F : Field A) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ContinuousOn (Function.uncurry F) (Set.Icc 0 T ×ˢ Set.univ)

end Operators

def gradient (p : ScalarField) : VectorField :=
  fun t q => WithLp.toLp 2 (fun i => spaceD i p t q)

def divergence (u : VectorField) : ScalarField :=
  fun t q => ∑ i : Fin 3, spaceD i (fun s x => u s x i) t q

def advection (u : VectorField) : VectorField :=
  fun t q => ∑ i : Fin 3, u t q i • spaceD i u t q

def Solenoidal (u : VectorField) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ q, divergence u t q = 0

def NavierStokes (ν : ℝ) (F u : VectorField) (p : ScalarField) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ q,
    timeD u t q + advection u t q =
      -gradient p t q + ν • laplacian u t q + F t q) ∧
  Solenoidal u ∧ ∀ q, u 0 q = 0

structure ClassicalSolution (ν : ℝ) (F u : VectorField) (p : ScalarField) : Prop where
  velocityContinuous : CylinderContinuous u
  timeDifferentiable : ∀ t : ℝ, 0 ≤ t → ∀ q,
    DifferentiableWithinAt ℝ (fun s => u s q) (Set.Ici (0 : ℝ)) t
  timeContinuous : CylinderContinuous (timeD u)
  spaceTwiceDifferentiable : ∀ t : ℝ, 0 ≤ t → ContDiff ℝ 2 (spaceLift u t)
  spaceFirstContinuous : ∀ i, CylinderContinuous (spaceD i u)
  spaceSecondContinuous : ∀ i j, CylinderContinuous (spaceD i (spaceD j u))
  pressureContinuous : CylinderContinuous p
  pressureDifferentiable : ∀ t : ℝ, 0 ≤ t → Differentiable ℝ (spaceLift p t)
  pressureGradientContinuous : CylinderContinuous (gradient p)
  pressureMeanZero : MeanZero p
  equations : NavierStokes ν F u p

def UniqueClassical (ν : ℝ) (F u : VectorField) (p : ScalarField) : Prop :=
  ∀ v q, ClassicalSolution ν F v q →
    ∀ t : ℝ, 0 ≤ t → (∀ x, v t x = u t x) ∧ (∀ x, q t x = p t x)

def IsParticle (u : VectorField) (X : ℝ → Space) : Prop :=
  X 0 = initialParticle ∧
  ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt X (u t (torusMk (X t))) (Set.Ici 0) t

def MaterialEvent (X : ℝ → Space) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ torusMk (X t) ∈ detector

abbrev Program := Nat.Partrec.Code
abbrev RationalPoint := ℚ × (Fin 3 → ℚ)

def accuracy (n : ℕ) : ℝ :=
  letI := twoAtLeastTwo
  (2 : ℝ) ^ (-(n : ℤ))

def ComputableReal (x : ℝ) : Prop :=
  ∃ P : Program, ∀ n : ℕ, ∃ q : ℚ,
    Encodable.encode q ∈ P.eval n ∧ |x - (q : ℝ)| ≤ accuracy n

def rationalVector (q : Fin 3 → ℚ) : Space :=
  WithLp.toLp 2 (fun i => (q i : ℝ))

def UniformlyEffective (F : Input → VectorField) : Prop :=
  ∃ modulus evaluate : Program,
    ∀ d : Input, d.WellFormed →
    ∀ (r : ℕ) (α : MultiIndex) (T n : ℕ),
      ∃ m : ℕ, m ∈ modulus.eval (Encodable.encode (d, r, α, T, n)) ∧
        ∀ a : RationalPoint, ∃ b : Fin 3 → ℚ,
          Encodable.encode b ∈ evaluate.eval (Encodable.encode (d, r, α, T, n, a)) ∧
          ∀ (t : ℝ) (x : Space), 0 ≤ t → t ≤ (T : ℝ) →
            |t - (a.1 : ℝ)| ≤ accuracy m →
            (∀ i, |x i - (a.2 i : ℝ)| ≤ accuracy m) →
            ‖mixedD r α (F d) t (torusMk x) - rationalVector b‖ ≤ accuracy n

def EffectiveConstants (C : Input → ℕ → MultiIndex → ℕ → ℕ) : Prop :=
  ∃ P : Program, ∀ d : Input, d.WellFormed → ∀ r α J,
    C d r α J ∈ P.eval (Encodable.encode (d, r, α, J))

def RapidPair (u F : VectorField) (C : ℕ → MultiIndex → ℕ → ℕ) : Prop :=
  ∀ (r J : ℕ) (α : MultiIndex) (t : ℝ), 0 ≤ t →
    spatialSup (mixedD r α u) t + spatialSup (mixedD r α F) t ≤
      (C r α J : ℝ) / (1 + t) ^ J

def UniqueMeanZeroPoisson (g : VectorField) (φ : ScalarField) : Prop :=
  ∀ ψ : ScalarField,
    (∀ t : ℝ, 0 ≤ t → ContDiff ℝ 2 (spaceLift ψ t)) → MeanZero ψ →
    (∀ t : ℝ, 0 ≤ t → ∀ q, laplacian ψ t q = divergence g t q) →
    ∀ t : ℝ, 0 ≤ t → ∀ q, ψ t q = φ t q

def LatticeConclusion (ν : ℝ) (d : Input)
    (U g f : VectorField) (φ : ScalarField)
    (C : ℕ → MultiIndex → ℕ → ℕ) : Prop :=
  Smooth U ∧ Smooth g ∧ Smooth f ∧ Smooth φ ∧
  MeanZero U ∧ MeanZero g ∧ MeanZero f ∧ MeanZero φ ∧
  ClassicalSolution ν g U 0 ∧
  ClassicalSolution ν f U (-φ) ∧
  RapidPair U g C ∧ RapidPair U f C ∧
  Solenoidal f ∧
  (∀ t : ℝ, 0 ≤ t → ∀ q, laplacian φ t q = divergence g t q) ∧
  UniqueMeanZeroPoisson g φ ∧
  (∀ t : ℝ, 0 ≤ t → ∀ q, f t q = g t q - gradient φ t q) ∧
  UniqueClassical ν g U 0 ∧ UniqueClassical ν f U (-φ) ∧
  ∃ X : ℝ → Space, IsParticle U X ∧
    (∀ Y : ℝ → Space, IsParticle U Y → ∀ t : ℝ, 0 ≤ t → Y t = X t) ∧
    (MaterialEvent X ↔ Halts d)

end
end PeriodicLattice

end OAI
