import Mathlib

namespace OAI

noncomputable section
namespace VelocityDetection
open scoped BigOperators Topology ContDiff
open Set Function Filter

abbrev Coord (n : ℕ) := Fin n → ℝ

abbrev ScalarField (n : ℕ) := ℝ → Coord n → ℝ

abbrev VectorField (n : ℕ) := ℝ → Coord n → Coord n

theorem neZeroTwo : NeZero 2 := ⟨Nat.succ_ne_zero 1⟩

theorem neZeroThree : NeZero 3 := ⟨Nat.succ_ne_zero 2⟩

theorem neZeroFive : NeZero 5 := ⟨Nat.succ_ne_zero 4⟩

def spatialD {n : ℕ} (i : Fin n) (q : ScalarField n) : ScalarField n :=
  fun t x => deriv (fun s => q t (Function.update x i s)) (x i)

def timeD {n : ℕ} (q : ScalarField n) : ScalarField n :=
  fun t x => derivWithin (fun s => q s x) (Ici 0) t

def laplacian {n : ℕ} (q : ScalarField n) : ScalarField n :=
  fun t x => ∑ i : Fin n, spatialD i (spatialD i q) t x

def advection {n : ℕ} (a : VectorField n) (q : ScalarField n) : ScalarField n :=
  fun t x => ∑ i : Fin n, a t x i * spatialD i q t x

def divergence {n : ℕ} (a : VectorField n) : ScalarField n :=
  fun t x => ∑ i : Fin n, spatialD i (fun s y => a s y i) t x

def NavierStokes (ν : ℝ) (u : VectorField 3) (p : ScalarField 3)
    (f : VectorField 3) : Prop :=
  (∀ (t : ℝ), 0 ≤ t → ∀ x : Coord 3, ∀ i : Fin 3,
    timeD (fun s y => u s y i) t x + advection u (fun s y => u s y i) t x =
      -spatialD i p t x + ν * laplacian (fun s y => u s y i) t x + f t x i) ∧
  (∀ (t : ℝ), 0 ≤ t → ∀ x, divergence u t x = 0) ∧
  (∀ x, u 0 x = 0)

def horizontal (x : Coord 3) : Coord 2 := ![x 0, x 1]

end VelocityDetection
end

noncomputable section
namespace VelocityDetection.Stacks
open scoped BigOperators Topology ContDiff
open Set Function Filter

inductive Move
  | right
  | stay
  | left
  deriving DecidableEq, Repr

def update (b : ℕ) (m : Move) (β x y : ℕ) : ℕ × ℕ :=
  match m with
  | .right => (b * x + β, y / b)
  | .stay => (x, y - y % b + β)
  | .left => (x / b, x % b + b * β + b ^ 2 * (y / b))

structure Rule (σ : Type*) (b : ℕ) where
  target : σ
  written : Fin b
  move : Move

structure Configuration (σ : Type*) where
  state : σ
  leftStack : ℕ
  rightStack : ℕ
  deriving DecidableEq

def applyRule {σ : Type*} {b : ℕ} (r : Rule σ b) (c : Configuration σ) : Configuration σ :=
  let st := update b r.move r.written c.leftStack c.rightStack
  ⟨r.target, st.1, st.2⟩

def address (B i x y : ℕ) : ℕ := 1 + x + B * y + B ^ 2 * i

def capacity (b m n : ℕ) : ℕ := b ^ (m + n)

end VelocityDetection.Stacks
end

noncomputable section
namespace VelocityDetection.Expanding
open scoped BigOperators Topology ContDiff
open Set Function Filter

def lambda (D : ℝ) : ℝ := 4 * D

def initialRadius (ν K D : ℝ) : ℝ :=
  1024 * 3000 * (1 + ν) * lambda D * (K * D + 2)

def radius (ν K D : ℝ) (n : ℕ) : ℝ := initialRadius ν K D * lambda D ^ n

end VelocityDetection.Expanding
end

noncomputable section
namespace VelocityDetection.Observation
open scoped BigOperators Topology ContDiff
open Set Function Filter
open MeasureTheory

def join (X : Coord 2) (z : ℝ) : Coord 3 := ![X 0, X 1, z]

def torusEvent (u : VectorField 3) : Prop :=
  letI := neZeroThree
  ∃ t : ℝ, 0 ≤ t ∧ ∃ x : Coord 3,
    1 / ((32 : ℕ) : ℝ) < x 1 ∧ x 1 < 1 / ((8 : ℕ) : ℝ) ∧ (1 / ((2 : ℕ) : ℝ) : ℝ) < u t x 2

def upperHalfPlane : Set (Coord 2) := {X | 0 < X 1}

def planeMass (u : VectorField 3) (t : ℝ) : ℝ :=
  letI := neZeroThree
  ∫ q in upperHalfPlane ×ˢ Ioc (0 : ℝ) 1,
    u t (join q.1 q.2) 2 ∂(volume.prod volume)

def planeEvent (u : VectorField 3) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ (1 / ((2 : ℕ) : ℝ) : ℝ) < planeMass u t

end VelocityDetection.Observation
end

noncomputable section
namespace VelocityDetection.SmoothProfiles
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff

abbrev step := Real.smoothTransition

end VelocityDetection.SmoothProfiles
end

noncomputable section
namespace VelocityDetection.TranslationGates
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open SmoothProfiles

def window (s : ℝ) : ℝ := step (s + 3) * step (3 - s)

end VelocityDetection.TranslationGates
end

noncomputable section
namespace VelocityDetection.CenterPaths
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open SmoothProfiles

def ramp (r : ℝ) : ℝ := step (2 * r - 1 / 2)

def theta (a T : ℝ) (j : ℕ) (t : ℝ) : ℝ := ramp (3 * (t - a) / T - j)

def privateRow (S : ℝ) (k : ℕ) : ℝ := -((k : ℝ) + 2) * S

def center (a T S S' σ : ℝ) (k l : ℕ) (t : ℝ) : Coord 2 :=
  ![(1 - theta a T 1 t) * S * k + theta a T 1 t * S' * l,
    -(1 - theta a T 0 t) * S +
      (theta a T 0 t - theta a T 2 t) * privateRow S k + theta a T 2 t * σ * S']

end VelocityDetection.CenterPaths
end

noncomputable section
namespace VelocityDetection.UniformDerivatives
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
variable {I E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def Bounded (f : I → E → F) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, ‖iteratedFDeriv ℝ n (f a) x‖ ≤ C

end VelocityDetection.UniformDerivatives
end

noncomputable section
namespace VelocityDetection.Stacks
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))

def lookup (c : Configuration (Fin N)) : Option (Rule (Fin N) b) :=
  table c.state ⟨c.rightStack % b, Nat.mod_lt _ hb⟩

end VelocityDetection.Stacks
end

noncomputable section
namespace VelocityDetection.TailSpace
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

def compatible (n : ℕ) : Submodule ℝ
    (C₀(Coord n, ℝ) × Lp ℝ 1 (volume : Measure (Coord n))) where
  carrier := {v | (fun X => v.2 X) =ᵐ[volume] (fun X => v.1 X)}
  zero_mem' := by exact Lp.coeFn_zero ..
  add_mem' := by
    intro v w hv hw
    change (fun X => (v.2 + w.2) X) =ᵐ[volume] (fun X => v.1 X + w.1 X)
    change (fun X => v.2 X) =ᵐ[volume] (fun X => v.1 X) at hv
    change (fun X => w.2 X) =ᵐ[volume] (fun X => w.1 X) at hw
    filter_upwards [Lp.coeFn_add v.2 w.2, hv, hw] with X hadd hvx hwx
    simpa [hvx, hwx] using hadd
  smul_mem' := by
    intro c v hv
    change (fun X => (c • v.2) X) =ᵐ[volume] (fun X => c * v.1 X)
    change (fun X => v.2 X) =ᵐ[volume] (fun X => v.1 X) at hv
    filter_upwards [Lp.coeFn_smul c v.2, hv] with X hsmul hvx
    simpa [hvx] using hsmul

end VelocityDetection.TailSpace
end

noncomputable section
namespace VelocityDetection.Cylinder
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

abbrev Space := Coord 2 × ℝ

abbrev Vect := Fin 3 → ℝ

def measure : Measure Space := volume.prod (volume.restrict (Ioc (0 : ℝ) 1))

def periodic (f : Space → ℝ) : Prop := ∀ X z, f (X, z + 1) = f (X, z)

def frame (i : Fin 3) : Space := ![(![1, 0], 0), (![0, 1], 0), (0, 1)] i

def D (i : Fin 3) (f : Space → ℝ) (x : Space) : ℝ := fderiv ℝ f x (frame i)

structure SliceH2 (v : Space → Vect) : Prop where
  smooth : ∀ i, ContDiff ℝ 2 (fun x => v x i)
  per : ∀ i, periodic (fun x => v x i)
  square_integrable : ∀ i, MemLp (fun x => v x i) 2 measure
  derivative_square_integrable : ∀ i k, MemLp (D k (fun x => v x i)) 2 measure
  second_square_integrable : ∀ i k l, MemLp (D l (D k (fun x => v x i))) 2 measure

structure PressureH1 (q : Space → ℝ) : Prop where
  smooth : ContDiff ℝ 1 q
  per : periodic q
  square_integrable : MemLp q 2 measure
  derivative_square_integrable : ∀ k, MemLp (D k q) 2 measure

theorem twoAtLeastTwo : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩

abbrev LpSpace {α : Type*} [MeasurableSpace α] (E : Type*) [NormedAddCommGroup E]
    (p : ENNReal) (μ : Measure α) : Type _ := Lp E p μ

abbrev L2Space : Type :=
  letI := twoAtLeastTwo
  LpSpace ℝ 2 measure

def dt (u : ℝ → Space → Vect) (t : ℝ) (x : Space) (i : Fin 3) : ℝ :=
  derivWithin (fun s => u s x i) (Ici 0) t

theorem spaceOuterMeasureClass : OuterMeasureClass (Measure Space) Space :=
  Measure.instOuterMeasureClass

def continuousL2On (g : ℝ → Space → ℝ) (T : ℝ) : Prop :=
  letI : IsTopologicalAddGroup ℝ := instIsTopologicalAddGroupReal
  letI := spaceOuterMeasureClass
  ∃ G : ℝ → L2Space, ContinuousOn G (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, (fun x => G t x) =ᵐ[measure] g t

def continuousH2On (u : ℝ → Space → Vect) (T : ℝ) : Prop :=
  (∀ t ∈ Icc 0 T, SliceH2 (u t)) ∧
  (∀ i, continuousL2On (fun t x => u t x i) T) ∧
  (∀ i k, continuousL2On (fun t => D k (fun x => u t x i)) T) ∧
  (∀ i k l, continuousL2On (fun t => D l (D k (fun x => u t x i))) T)

def continuousH1On (p : ℝ → Space → ℝ) (T : ℝ) : Prop :=
  (∀ t ∈ Icc 0 T, PressureH1 (p t)) ∧ continuousL2On p T ∧
  (∀ i, continuousL2On (fun t => D i (p t)) T)

def C1L2On (u : ℝ → Space → Vect) (T : ℝ) : Prop :=
  letI : IsTopologicalAddGroup ℝ := instIsTopologicalAddGroupReal
  letI := spaceOuterMeasureClass
  ∃ U dU : ℝ → Fin 3 → L2Space,
    (∀ i, ContinuousOn (fun t => U t i) (Icc 0 T)) ∧
    (∀ i, ContinuousOn (fun t => dU t i) (Icc 0 T)) ∧
    (∀ t ∈ Icc 0 T, ∀ i, (fun x => U t i x) =ᵐ[measure] (fun x => u t x i)) ∧
    (∀ t ∈ Icc 0 T, ∀ i, (fun x => dU t i x) =ᵐ[measure] (fun x => dt u t x i)) ∧
    (∀ t ∈ Icc 0 T, ∀ i,
      HasDerivWithinAt (fun s => U s i) (dU t i) (Icc 0 T) t)

structure ComparisonClass (u : ℝ → Space → Vect) (p : ℝ → Space → ℝ) : Prop where
  velocity_H2 : ∀ T > 0, continuousH2On u T
  velocity_C1L2 : ∀ T > 0, C1L2On u T
  pressure_H1 : ∀ T > 0, continuousH1On p T
  time_derivative : ∀ t ≥ 0, ∀ x i,
    HasDerivWithinAt (fun s => u s x i) (dt u t x i) (Ici 0) t
  velocity_continuous : ∀ T > 0, ∀ i,
    ContinuousOn (fun y : ℝ × Space => u y.1 y.2 i) (Icc 0 T ×ˢ univ)
  time_continuous : ∀ T > 0, ∀ i,
    ContinuousOn (fun y : ℝ × Space => dt u y.1 y.2 i) (Icc 0 T ×ˢ univ)
  gradient_continuous : ∀ T > 0, ∀ i k,
    ContinuousOn (fun y : ℝ × Space => D k (fun x => u y.1 x i) y.2) (Icc 0 T ×ˢ univ)
  second_continuous : ∀ T > 0, ∀ i k l,
    ContinuousOn (fun y : ℝ × Space => D l (D k (fun x => u y.1 x i)) y.2) (Icc 0 T ×ˢ univ)
  pressure_continuous : ∀ T > 0,
    ContinuousOn (fun y : ℝ × Space => p y.1 y.2) (Icc 0 T ×ˢ univ)
  pressure_gradient_continuous : ∀ T > 0, ∀ i,
    ContinuousOn (fun y : ℝ × Space => D i (p y.1) y.2) (Icc 0 T ×ˢ univ)
  bounds : ∀ T > 0, ∃ B : ℝ, 0 ≤ B ∧
    (∀ t ∈ Icc 0 T, ∀ x i, |u t x i| ≤ B) ∧
    (∀ t ∈ Icc 0 T, ∀ x i k, |D k (fun y => u t y i) x| ≤ B)

def join (x : Space) : Coord 3 :=
  letI := neZeroTwo
  ![x.1 0, x.1 1, x.2]

end VelocityDetection.Cylinder
end

noncomputable section
namespace VelocityDetection.TailSpace
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

def evalLinear (X : Coord 2) : compatible 2 →ₗ[ℝ] ℝ where
  toFun f := f.val.1 X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def eval (X : Coord 2) : compatible 2 →L[ℝ] ℝ where
  toLinearMap := evalLinear X
  cont := AddMonoidHomClass.continuous_of_bound (evalLinear X) 1 (fun f => by
    change ‖f.val.1 X‖ ≤ 1 * ‖f.val‖
    rw [one_mul]
    exact (BoundedContinuousFunction.norm_coe_le_norm f.val.1.toBCF X).trans (norm_fst_le f.val))

end VelocityDetection.TailSpace
end

noncomputable section
namespace VelocityDetection.History
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open Stacks

structure Configuration (N : ℕ) where
  tape : Stacks.Configuration (Fin N)
  history : ℕ
  deriving DecidableEq

end VelocityDetection.History
end

noncomputable section
namespace VelocityDetection.History
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open Stacks
variable {N b : ℕ} (hb : 0 < b)
  (table : Fin N → Fin b → Option (Rule (Fin N) b))

def radix (N b : ℕ) : ℕ := N * b

def tag (c : Stacks.Configuration (Fin N)) : ℕ := b * c.state.val + c.rightStack % b

include hb in

def applyRule (r : Rule (Fin N) b) (c : Configuration N) : Configuration N :=
  ⟨Stacks.applyRule r c.tape, radix N b * c.history + tag (b := b) c.tape⟩

include hb in

def packedState (c : Configuration N) : ℕ := N * c.history + c.tape.state.val

def address (B : ℕ) (c : Configuration N) : ℕ :=
  Stacks.address B (packedState c) c.tape.leftStack c.tape.rightStack

abbrev Box (N B H : ℕ) := Fin N × Fin B × Fin B × Fin H

def config {B H : ℕ} (c : Box N B H) : Configuration N :=
  ⟨⟨c.1, c.2.1, c.2.2.1⟩, c.2.2.2⟩

def Active (B H : ℕ) := {c : Box N B H // (Stacks.lookup hb table (config c).tape).isSome}

def rule {B H : ℕ} (c : Active hb table B H) : Rule (Fin N) b :=
  (Stacks.lookup hb table (config c.val).tape).get c.property

def target {B H : ℕ} (c : Active hb table B H) : Configuration N :=
  applyRule (rule hb table c) (config c.val)

def sourceAddress {B H : ℕ} (c : Active hb table B H) : ℕ := address B (config c.val)

def targetAddress {B H : ℕ} (c : Active hb table B H) : ℕ := address (b * B) (target hb table c)

end VelocityDetection.History
end

noncomputable section
namespace VelocityDetection.TapeCodes
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open Turing Stacks
variable {b N : ℕ} [NeZero b] [NeZero N]

def word (w : List (Fin b)) : ℕ := Nat.ofDigits b (w.map Fin.val)

def half (w : ListBlank (Fin b)) : ℕ :=
  w.liftOn word (by sorry)

def tape (q : Fin N) (T : Tape (Fin b)) : Stacks.Configuration (Fin N) :=
  ⟨q, half T.left, half T.right₀⟩

def rule (a : Fin b) (q : Fin N) : TM0.Stmt (Fin b) → Rule (Fin N) b
  | .move .left => ⟨q, a, .left⟩
  | .move .right => ⟨q, a, .right⟩
  | .write β => ⟨q, β, .stay⟩

def table (M : TM0.Machine (Fin b) (Fin N)) : Fin N → Fin b → Option (Rule (Fin N) b) :=
  fun q a => (M q a).map (fun p => rule a p.1 p.2)

end VelocityDetection.TapeCodes
end

noncomputable section
namespace VelocityDetection.Prelude
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open Stacks
variable {N b : ℕ} (hb : 0 < b)
  (table : Fin N → Fin b → Option (Rule (Fin N) b)) (q₀ : Fin N)

def rule (r : Rule (Fin N) b) : Rule (Fin (N + 1)) b :=
  ⟨r.target.castSucc, r.written, r.move⟩

def table' : Fin (N + 1) → Fin b → Option (Rule (Fin (N + 1)) b) :=
  Fin.lastCases (fun a => some ⟨q₀.castSucc, a, .stay⟩)
    (fun q a => (table q a).map rule)

def initial (x y : ℕ) : Configuration (Fin (N + 1)) := ⟨Fin.last N, x, y⟩

end VelocityDetection.Prelude
end

noncomputable section
namespace VelocityDetection.MachineHistory
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open Turing Stacks
variable {b N : ℕ} [NeZero b] [NeZero N]

def table (M : TM0.Machine (Fin b) (Fin N)) :
    Fin (N + 1) → Fin b → Option (Rule (Fin (N + 1)) b) :=
  Prelude.table' (TapeCodes.table M) 0

def initial (w : List (Fin b)) : Stacks.Configuration (Fin (N + 1)) :=
  Prelude.initial 0 (TapeCodes.word w)

end VelocityDetection.MachineHistory
end

noncomputable section
namespace VelocityDetection.Effective
open Polynomial Set Function Filter
open scoped BigOperators Topology ContDiff

abbrev Poly := List (ℕ × ℚ)

noncomputable def poly : Poly → Polynomial ℝ
  | [] => 0
  | (k,q)::ps => Polynomial.C (q:ℝ)*Polynomial.X^k + poly ps

def nextPoly : Poly → Poly
  | [] => []
  | (k,q)::ps => (k+2,q)::(k+1,-q*k)::nextPoly ps

noncomputable def flat (p : Poly) (x : ℝ) : ℝ :=
  (poly p).eval x⁻¹ * expNegInvGlue x

def polyBound : Poly → ℚ
  | [] => 0
  | (k,q)::ps => |q| *k.factorial + polyBound ps

inductive Expr (n : ℕ) where
  | rat : ℚ → Expr n
  | var : Fin n → Expr n
  | add : Expr n → Expr n → Expr n
  | neg : Expr n → Expr n
  | mul : Expr n → Expr n → Expr n
  | inv : Expr n → Expr n
  | flat : Poly → Expr n → Expr n
  deriving Inhabited

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.Effective.Expr
open Polynomial Set Function Filter
open scoped BigOperators Topology ContDiff
variable {n : ℕ}

noncomputable def eval (x : Fin n → ℝ) : Expr n → ℝ
  | .rat q => q
  | .var i => x i
  | .add a b => a.eval x + b.eval x
  | .neg a => -a.eval x
  | .mul a b => a.eval x * b.eval x
  | .inv a => (a.eval x)⁻¹
  | .flat p a => Effective.flat p (a.eval x)

def diff (i : Fin n) : Expr n → Expr n
  | .rat _ => .rat 0
  | .var j => .rat (if i=j then 1 else 0)
  | .add a b => .add (a.diff i) (b.diff i)
  | .neg a => .neg (a.diff i)
  | .mul a b => .add (.mul (a.diff i) b) (.mul a (b.diff i))
  | .inv a => .neg (.mul (a.diff i) (.mul (.inv a) (.inv a)))
  | .flat p a => .mul (.flat (nextPoly p) a) (a.diff i)

def jet : List (Fin n) → Expr n → Expr n
  | [], e => e
  | i::is, e => jet is (e.diff i)

end VelocityDetection.Effective.Expr
end

noncomputable section
namespace VelocityDetection.Effective
open Set Filter Function
open scoped BigOperators Topology

structure Ball where
  center : ℚ
  radius : ℚ
  deriving Inhabited

def polyEval : Poly → ℚ → ℚ
  | [], _ => 0
  | (k,q)::ps, x => q*x^k+polyEval ps x

def expSum (q : ℚ) (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, q^k / k.factorial

def expError (q : ℚ) (n : ℕ) : ℚ := |q|^n / n.factorial * 2

def flatRound (p : Poly) (q : ℚ) (n : ℕ) : Ball :=
  if q ≤ 0 then ⟨0,0⟩ else
  if |q⁻¹|/(n+1) ≤ (1/2:ℚ) ∧
      |polyEval p q⁻¹| *expError (-q⁻¹) n ≤ polyBound (nextPoly p)*|q| then
    ⟨polyEval p q⁻¹*expSum (-q⁻¹) n,|polyEval p q⁻¹| *expError (-q⁻¹) n⟩
  else ⟨0,polyBound (nextPoly p)*|q|⟩

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.Effective.Ball
open Set Filter Function
open scoped Topology

def atom (q : ℚ) : Ball := ⟨q,0⟩

def add (a b : Ball) : Ball := ⟨a.center+b.center,a.radius+b.radius⟩

def neg (a : Ball) : Ball := ⟨-a.center,a.radius⟩

def mul (a b : Ball) : Ball :=
  ⟨a.center*b.center,|a.center| *b.radius+|b.center| *a.radius+a.radius*b.radius⟩

def inv (a : Ball) : Ball :=
  ⟨a.center⁻¹,a.radius/(|a.center| *(|a.center|-a.radius))⟩

def invSafe (a : Ball) : Bool := decide (a.radius < |a.center|)

def flat (p : Poly) (a : Ball) (k : ℕ) : Ball :=
  let b := flatRound p a.center k
  ⟨b.center,b.radius+polyBound (nextPoly p)*a.radius⟩

end VelocityDetection.Effective.Ball
end

noncomputable section
namespace VelocityDetection.Effective.Expr
open Set Filter Function
open scoped Topology
variable {n : ℕ}

def round (a : Fin n → Ball) (k : ℕ) : Expr n → Ball :=
  Expr.rec (motive := fun _ => Ball)
    Ball.atom a
    (fun _ _ e f => e.add f)
    (fun _ e => e.neg)
    (fun _ _ e f => e.mul f)
    (fun _ e => e.inv)
    (fun p _ e => e.flat p k)

def safe (a : Fin n → Ball) (k : ℕ) : Expr n → Bool :=
  Expr.rec (motive := fun _ => Bool)
    (fun _ => true) (fun _ => true)
    (fun _ _ e f => e && f)
    (fun _ e => e)
    (fun _ _ e f => e && f)
    (fun e safe_e => safe_e && (e.round a k).invSafe)
    (fun _ _ e => e)

end VelocityDetection.Effective.Expr
end

noncomputable section
namespace VelocityDetection.Effective
open Set Filter Function
open scoped Topology

noncomputable def coordinateD {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun s => f (update x i s)) (x i)

noncomputable def mixedD {n : ℕ} : List (Fin n) → ((Fin n → ℝ) → ℝ) → (Fin n → ℝ) → ℝ
  | [], f => f
  | i::is, f => mixedD is (coordinateD i f)

def accuracy (k : ℕ) : ℚ := (1/2)^k

def Names {n : ℕ} (q : Fin n → ℕ → ℚ) (x : Fin n → ℝ) : Prop :=
  ∀ i k, |x i-(q i k:ℝ)| ≤ (accuracy k:ℝ)

def inputBall {n : ℕ} (q : Fin n → ℕ → ℚ) (k : ℕ) (i : Fin n) : Ball :=
  ⟨q i k,accuracy k⟩

def trial {n : ℕ} (e : Expr n) (is : List (Fin n)) (q : Fin n → ℕ → ℚ)
    (ε : ℚ) (k : ℕ) : Option ℚ :=
  let d := e.jet is
  let a := inputBall q k
  if d.safe a k && decide ((d.round a k).radius ≤ ε) then some (d.round a k).center else none

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.PeriodicSpace
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction

abbrev Torus (n : ℕ) := Fin n → AddCircle (1 : ℝ)

def cover {n : ℕ} (X : Coord n) : Torus n := fun i => (X i : AddCircle (1 : ℝ))

end VelocityDetection.PeriodicSpace
end

noncomputable section
namespace VelocityDetection.SmoothBump
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open TranslationGates

def profile (s : ℝ) : ℝ := window (((3 : ℕ) : ℝ)*s)

end VelocityDetection.SmoothBump
end

noncomputable section
namespace VelocityDetection.TorusClass
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators

abbrev Space := Coord 3

def measure : Measure Space := volume.restrict (Icc (0 : Space) 1)

def periodic (f : Space → ℝ) : Prop := FactorsThrough f PeriodicSpace.cover

def frame (i : Fin 3) : Space := Pi.single i 1

def D (i : Fin 3) (f : Space → ℝ) (x : Space) : ℝ := fderiv ℝ f x (frame i)

def dt (u : VectorField 3) (t : ℝ) (x : Space) (i : Fin 3) : ℝ :=
  derivWithin (fun s => u s x i) (Ici 0) t

structure ComparisonClass (u : VectorField 3) (p : ScalarField 3) : Prop where
  velocity_slices : ∀ t ≥ 0, ∀ i, ContDiff ℝ 2 (fun x => u t x i)
  pressure_slices : ∀ t ≥ 0, ContDiff ℝ 1 (p t)
  velocity_periodic : ∀ t ≥ 0, FactorsThrough (u t) PeriodicSpace.cover
  pressure_periodic : ∀ t ≥ 0, periodic (p t)
  pressure_mean : ∀ t ≥ 0, (∫ x, p t x ∂measure) = 0
  time_derivative : ∀ t ≥ 0, ∀ x i,
    HasDerivWithinAt (fun s => u s x i) (dt u t x i) (Ici 0) t
  velocity_continuous : ∀ T > 0, ∀ i,
    ContinuousOn (fun y : ℝ × Space => u y.1 y.2 i) (Icc 0 T ×ˢ univ)
  time_continuous : ∀ T > 0, ∀ i,
    ContinuousOn (fun y : ℝ × Space => dt u y.1 y.2 i) (Icc 0 T ×ˢ univ)
  gradient_continuous : ∀ T > 0, ∀ i k,
    ContinuousOn (fun y : ℝ × Space => D k (fun x => u y.1 x i) y.2) (Icc 0 T ×ˢ univ)
  second_continuous : ∀ T > 0, ∀ i k l,
    ContinuousOn (fun y : ℝ × Space => D l (D k (fun x => u y.1 x i)) y.2) (Icc 0 T ×ˢ univ)
  pressure_continuous : ∀ T > 0,
    ContinuousOn (fun y : ℝ × Space => p y.1 y.2) (Icc 0 T ×ˢ univ)
  pressure_gradient_continuous : ∀ T > 0, ∀ i,
    ContinuousOn (fun y : ℝ × Space => D i (p y.1) y.2) (Icc 0 T ×ˢ univ)

end VelocityDetection.TorusClass
end

noncomputable section
namespace VelocityDetection.MachineTorus
open Set Function MeasureTheory
open scoped Topology ContDiff BigOperators
open Turing Stacks
variable {b N : ℕ} [NeZero b] [NeZero N]

def initialAddress (w : List (Fin b)) : ℕ :=
  History.address (capacity b (w.length+1) 0) ⟨MachineHistory.initial (N := N) w,0⟩

end VelocityDetection.MachineTorus
end

noncomputable section
namespace VelocityDetection.Effective.Expr
open Set Function Filter
open scoped Topology BigOperators
variable {n m : ℕ}

instance : Add (Expr n) := ⟨Expr.add⟩

instance : Neg (Expr n) := ⟨Expr.neg⟩

instance : Sub (Expr n) := ⟨fun a b => .add a (.neg b)⟩

instance : Mul (Expr n) := ⟨Expr.mul⟩

instance : Inv (Expr n) := ⟨Expr.inv⟩

instance : Div (Expr n) := ⟨fun a b => .mul a (.inv b)⟩

instance (k : ℕ) : OfNat (Expr n) k := ⟨.rat k⟩

def subst (v : Fin m → Expr n) : Expr m → Expr n :=
  Expr.rec (motive := fun _ => Expr n)
    Expr.rat v
    (fun _ _ a b => .add a b)
    (fun _ a => .neg a)
    (fun _ _ a b => .mul a b)
    (fun _ a => .inv a)
    (fun p _ a => .flat p a)

def sumList : List (Expr n) → Expr n
  | [] => 0
  | e::es => e + sumList es

def sumFin (k : ℕ) (f : Fin k → Expr n) : Expr n := sumList (List.ofFn f)

def unaryD (e : Expr 1) (a : Expr n) : Expr n := (e.diff 0).subst (fun _ => a)

end VelocityDetection.Effective.Expr
end

noncomputable section
namespace VelocityDetection.Effective.Recipe
open Set Function Filter
open scoped Topology BigOperators
open _root_.OAI.VelocityDetection.Effective.Expr
variable {n : ℕ}

def glue (a : Expr n) : Expr n := .flat [(0,1)] a

def step (a : Expr n) : Expr n := glue a/(glue a+glue (1-a))

def pulse (a : Expr n) : Expr n := (step (.var 0 : Expr 1)).unaryD a

def window (a : Expr n) : Expr n := step (a+3)*step (3-a)

def windowD (a : Expr n) : Expr n := pulse (a+3)*step (3-a)-step (a+3)*pulse (3-a)

def theta (a T : Expr n) (j : ℕ) (t : Expr n) : Expr n :=
  step (2*(3*(t-a)/T-.rat j)-.rat (1/2))

def center (a T S S' σ : Expr n) (k l : ℕ) (t : Expr n) : Fin 2 → Expr n :=
  ![(1-theta a T 1 t)*S*.rat k+theta a T 1 t*S'*.rat l,
    -(1-theta a T 0 t)*S+(theta a T 0 t-theta a T 2 t)*(-(.rat k+2)*S)+
      theta a T 2 t*σ*S']

def gate (R : Expr n) (c G X : Fin 2 → Expr n) : Fin 2 → Expr n :=
  letI := neZeroTwo
  ![window ((X 0-c 0)/R)*(windowD ((X 1-c 1)/R)/R)*
      (G 0*(X 1-c 1)-G 1*(X 0-c 0))+
      window ((X 0-c 0)/R)*window ((X 1-c 1)/R)*G 0,
    window ((X 0-c 0)/R)*window ((X 1-c 1)/R)*G 1-
      (windowD ((X 0-c 0)/R)/R*window ((X 1-c 1)/R))*
        (G 0*(X 1-c 1)-G 1*(X 0-c 0))]

def impulse (t : Expr n) (p X : Fin 2 → Expr n) : Expr n :=
  letI := neZeroTwo
  pulse t*pulse (X 0-p 0+.rat (1/2))*pulse (X 1-p 1+.rat (1/2))

def packet (R : Expr n) (X : Fin 2 → Expr n) : Expr n :=
  letI := neZeroTwo
  window (3*(X 0/R))*window (3*(X 1/R))

end VelocityDetection.Effective.Recipe
end

noncomputable section
namespace VelocityDetection.Effective.Expr
open Set Function
open scoped BigOperators Topology
variable {n : ℕ}

def activeSum {N b B H : ℕ} (hb : 0 < b)
    (table : Fin N → Fin b → Option (Stacks.Rule (Fin N) b))
    (f : History.Active hb table B H → Expr n) : Expr n :=
  sumFin N (fun s => sumFin B (fun l => sumFin B (fun r => sumFin H (fun h =>
    if hp : (Stacks.lookup hb table (History.config (s,l,r,h)).tape).isSome then
      f ⟨(s,l,r,h),hp⟩ else 0))))

end VelocityDetection.Effective.Expr
end

noncomputable section
namespace VelocityDetection.Effective.ArrayRecipe
open Set Function
open scoped BigOperators Topology
open _root_.OAI.VelocityDetection.Effective.Expr Stacks
variable {N b : ℕ} (hN : 0 < N) (hb : 0 < b)
  (table : Fin N → Fin b → Option (Rule (Fin N) b)) (m : ℕ)

abbrev Code := Expr 5

def K (N b m : ℕ) : ℕ := N * capacity b (m+1) 0 ^ 2

def D (N b : ℕ) : ℕ := b^2 * History.radix N b

def radius (N b m n : ℕ) : Code :=
  .rat (1024*3000*(4*(D N b))*(K N b m*D N b+2)*(4*D N b)^n) * (1+.var 0)

def spacing (N b m n : ℕ) : Code := 16*radius N b m n

def duration (N b m n : ℕ) : Code :=
  spacing N b m (n+1) * .rat (K N b m*D N b^(n+1)+2)

def start (N b m : ℕ) : ℕ → Code
  | 0 => 1
  | n+1 => start N b m n+duration N b m n

def sign (c : History.Configuration N) : ℚ :=
  if (lookup hb table c.tape).isNone then 1 else -1

abbrev Instruction (n : ℕ) := History.Active hb table (capacity b (m+1) n) (History.radix N b^n)

def path (n : ℕ) (c : Instruction hb table m n) : Fin 2 → Code :=
  Recipe.center (start N b m n) (duration N b m n) (spacing N b m n)
    (spacing N b m (n+1)) (.rat (sign hb table (History.target hb table c)))
    (History.sourceAddress hb table c) (History.targetAddress hb table c) (.var 1)

def gate (n : ℕ) (c : Instruction hb table m n) : Fin 2 → Code :=
  Recipe.gate (radius N b m n) (path hb table m n c)
    (fun i => (path hb table m n c i).diff 1) ![.var 2,.var 3]

def stage (n : ℕ) (i : Fin 2) : Code :=
  activeSum hb table (fun c : Instruction hb table m n => gate hb table m n c i)

def field (L : ℕ) (i : Fin 2) : Code := sumFin L (fun n => stage hb table m n i)

end VelocityDetection.Effective.ArrayRecipe
end

noncomputable section
namespace VelocityDetection.Effective.ChartRecipe
open Set Function ArrayRecipe
open scoped BigOperators Topology
open VelocityDetection.Effective.Expr
variable {N b : ℕ} (hN : 0 < N) (hb : 0 < b)
  (table : Fin N → Fin b → Option (Stacks.Rule (Fin N) b)) (m : ℕ)

def scale (N b m P : ℕ) : ℚ := (1024*((K N b m:ℚ)*(D N b:ℚ)^(P+1)+4))⁻¹

def radius (N b m P : ℕ) : ℚ := scale N b m P/16

def targetHeight (P n : ℕ) (c : Instruction hb table m n) : ℚ :=
  if ArrayRecipe.sign hb table (History.target hb table c) = 1 then -(7/16) else -scale N b m P

def path (P n : ℕ) (c : Instruction hb table m n) : Fin 2 → Code :=
  letI := neZeroFive
  fun i =>
    .rat (![1/4,1/2] i) + Recipe.center (.rat n) 1 (.rat (scale N b m P)) (.rat (scale N b m P))
      (.rat (targetHeight hb table m P n c/scale N b m P))
      (History.sourceAddress hb table c) (History.targetAddress hb table c) (.var 1) i

def gate (P n : ℕ) (c : Instruction hb table m n) : Fin 2 → Code :=
  letI := neZeroFive
  Recipe.gate (.rat (radius N b m P)) (path hb table m P n c)
    (fun i => (path hb table m P n c i).diff 1) ![.var 2,.var 3]

def stage (P n : ℕ) (i : Fin 2) : Code :=
  activeSum hb table (fun c : Instruction hb table m n => gate hb table m P n c i)

def prefixCode (P : ℕ) (i : Fin 2) : Code := sumFin P (fun n => stage hb table m P n i)

def duration (N b m B k : ℕ) : Code :=
  letI := neZeroFive
  .rat ((1/16)*(1/2:ℚ)^k) /
    (3*(1+.var 0*.rat (2*(B:ℚ)/(radius N b m (k+1))^2)))

def localTime (N b m B k : ℕ) : Code :=
  letI := neZeroFive
  (.var 1-.rat (k+1))/duration N b m B k

def weight (N b m B k : ℕ) : Code :=
  Recipe.step (8*localTime N b m B k)-Recipe.step (8*localTime N b m B k-.rat 7)

def clock (N b m B k : ℕ) : Code := .rat (k+1)*
  (Recipe.step (8*localTime N b m B k-1)-Recipe.step (8*localTime N b m B k-.rat 5))

def rawField (B k : ℕ) (i : Fin 2) : Code :=
  letI := neZeroFive
  (clock N b m B k).diff 1 * (prefixCode hb table m (k+1) i).subst
    ![.var 0,clock N b m B k,.var 2,.var 3,.var 4]

def initial (N b m P q : ℕ) : Fin 2 → Code :=
  ![.rat (1/4+scale N b m P*q),.rat (1/2-scale N b m P)]

def rawSource (B q k : ℕ) : Code :=
  letI := neZeroFive
  (weight N b m B k).diff 1 *
    Recipe.packet (.rat (radius N b m (k+1)))
      (fun i => (![.var 2,.var 3] i)-initial N b m (k+1) q i)

end VelocityDetection.Effective.ChartRecipe
end

noncomputable section
namespace VelocityDetection.Effective
open Set Function
open scoped Topology BigOperators
open _root_.OAI.VelocityDetection.Effective.Expr ArrayRecipe

def periodize (R : ℕ) (e : Code) : Code :=
  letI := neZeroFive
  sumFin (2*R+1) (fun i => sumFin (2*R+1) (fun j =>
    e.subst ![.var 0,.var 1,.var 2-.rat ((i:ℚ)-R),.var 3-.rat ((j:ℚ)-R),.var 4]))

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.Effective.ChartRecipe
open Set Function
open scoped Topology BigOperators
open _root_.OAI.VelocityDetection.Effective.Expr ArrayRecipe
variable {N b : ℕ} (hN : 0 < N) (hb : 0 < b)
  (table : Fin N → Fin b → Option (Stacks.Rule (Fin N) b)) (m : ℕ)

def fieldBlock (B R k : ℕ) (i : Fin 2) : Code := periodize R (rawField hb table m B k i)

def sourceBlock (N b m B q R k : ℕ) : Code := periodize R (rawSource (N:=N) (b:=b) m B q k)

def field (B R L : ℕ) (i : Fin 2) : Code := sumFin L (fun k => fieldBlock hb table m B R k i)

def source (N b m B q R L : ℕ) : Code := sumFin L (fun k => sourceBlock N b m B q R k)

end VelocityDetection.Effective.ChartRecipe
end

noncomputable section
namespace VelocityDetection.Effective
open Set Filter Function
open scoped Topology BigOperators ContDiff
open VelocityDetection.Effective.Expr ArrayRecipe

def residualCode (a : Fin 2 → Code) (i : Fin 2) : Code :=
  letI := neZeroTwo
  letI := neZeroFive
  (a i).diff 1 + a 0*(a i).diff 2 + a 1*(a i).diff 3 -
    .var 0*((((a i).diff 2).diff 2)+(((a i).diff 3).diff 3))

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.Effective.ArrayRecipe
open Set Filter Function Turing
open scoped Topology BigOperators ContDiff
open VelocityDetection.Effective.Expr ArrayRecipe

def initialCode (N b m q : ℕ) : Fin 2 → Code :=
  ![spacing N b m 0 * .rat q,-spacing N b m 0]

def source (N b m q : ℕ) : Code :=
  letI := neZeroFive
  Recipe.impulse (.var 1) (initialCode N b m q) ![.var 2,.var 3]

end VelocityDetection.Effective.ArrayRecipe
end

noncomputable section
namespace VelocityDetection.Effective
open Set Filter Function Turing
open scoped Topology BigOperators ContDiff
open VelocityDetection.Effective.Expr ArrayRecipe

noncomputable def forceFunction (f : ℝ → VectorField 3) (i : Fin 3) (x : Fin 5 → ℝ) : ℝ :=
  letI := neZeroFive
  f (x 0) (x 1) ![x 2,x 3,x 4] i

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.Effective.MachineRecipe
open Set Filter Function Turing
open scoped Topology BigOperators ContDiff
open VelocityDetection.Effective.Expr ArrayRecipe
variable {b N : ℕ} [NeZero b] [NeZero N]

inductive Domain where | torus | cylinder
  deriving DecidableEq, Repr

def field (d : Domain) (B R L : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (i : Fin 2) : Code := match d with
  | .torus => ChartRecipe.field (NeZero.pos b) (MachineHistory.table M) w.length B R L i
  | .cylinder => ArrayRecipe.field (NeZero.pos b) (MachineHistory.table M) w.length L i

def source (d : Domain) (B R L : ℕ) (w : List (Fin b)) : Code := match d with
  | .torus => ChartRecipe.source (N+1) b w.length B (MachineTorus.initialAddress (N:=N) w) R L
  | .cylinder => ArrayRecipe.source (N+1) b w.length (MachineTorus.initialAddress (N:=N) w)

def force (d : Domain) (B R L : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (i : Fin 3) : Code :=
  letI := neZeroTwo
  ![residualCode (field d B R L M w) 0,residualCode (field d B R L M w) 1,
    source (N:=N) d B R L w] i

end VelocityDetection.Effective.MachineRecipe
end

noncomputable section
namespace VelocityDetection.Effective.MachineRecipe
open Set Filter Function Turing
open scoped Topology ContDiff BigOperators
variable {b N : ℕ} [NeZero b] [NeZero N]

def timeCutoff (q : Fin 5 → ℕ → ℚ) : ℕ :=
  letI := neZeroFive
  ⌈q 1 0+2⌉₊

def spaceCutoff (q : Fin 5 → ℕ → ℚ) : ℕ :=
  letI := neZeroFive
  ⌈|q 2 0|+|q 3 0|+3⌉₊

def runTrial (d : Domain) (B : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (i : Fin 3) (is : List (Fin 5)) (q : Fin 5 → ℕ → ℚ)
    (ε : ℚ) (k : ℕ) : Option ℚ :=
  trial (force d B (spaceCutoff q) (timeCutoff q) M w i) is q ε k

end VelocityDetection.Effective.MachineRecipe
end

noncomputable section
namespace VelocityDetection.Effective
open Set Filter Function
open scoped Topology BigOperators

structure RationalBox (n : ℕ) where
  lower : Fin n → ℚ
  upper : Fin n → ℚ
  ordered : ∀ i, lower i ≤ upper i

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection.Effective.RationalBox
open Set Filter Function
open scoped Topology BigOperators
variable {n : ℕ} (Q : RationalBox n)

def carrier : Set (Fin n → ℝ) := Icc (fun i => (Q.lower i:ℝ)) (fun i => (Q.upper i:ℝ))

def cell (k : ℕ) (j : Fin n → Fin (k+2)) (i : Fin n) : Ball :=
  ⟨Q.lower i+(Q.upper i-Q.lower i)*((j i:ℕ):ℚ)/(k+1),
    (Q.upper i-Q.lower i)/(k+1)⟩

def boundTrial (e : Expr n) (is : List (Fin n)) (k : ℕ) : Option ℚ :=
  if ∀ j : Fin n → Fin (k+2), (e.jet is).safe (Q.cell k j) k = true then
    some (∑ j : Fin n → Fin (k+2),
      (|((e.jet is).round (Q.cell k j) k).center| + |((e.jet is).round (Q.cell k j) k).radius|))
  else none

end VelocityDetection.Effective.RationalBox
end

noncomputable section
namespace VelocityDetection.Effective.MachineRecipe
open Set Function Turing
variable {b N : ℕ} [NeZero b] [NeZero N]

def boxTimeCutoff (Q : RationalBox 5) : ℕ :=
  letI := neZeroFive
  ⌈Q.upper 1+1⌉₊

def boxSpaceCutoff (Q : RationalBox 5) : ℕ :=
  letI := neZeroFive
  ⌈|Q.lower 2|+|Q.upper 2|+|Q.lower 3|+|Q.upper 3|+2⌉₊

def runBoundTrial (d : Domain) (B : ℕ) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (i : Fin 3) (is : List (Fin 5)) (Q : RationalBox 5) (k : ℕ) : Option ℚ :=
  Q.boundTrial (force d B (boxSpaceCutoff Q) (boxTimeCutoff Q) M w i) is k

end VelocityDetection.Effective.MachineRecipe
end

noncomputable section
namespace VelocityDetection.Effective.MachineRecipe
open Turing

structure Program (b N : ℕ) [NeZero b] [NeZero N] where
  derivativeBound : ℕ
  table : TM0.Machine (Fin b) (Fin N)
  input : List (Fin b)

def compile {b N : ℕ} [NeZero b] [NeZero N] (B : ℕ) (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) :
    Program b N := ⟨B,M,w⟩

end VelocityDetection.Effective.MachineRecipe
end

noncomputable section
namespace VelocityDetection.Effective.MachineRecipe.Program
open Turing
variable {b N : ℕ} [NeZero b] [NeZero N]

def valueTrial (P : Program b N) (d : Domain) (i : Fin 3) (is : List (Fin 5))
    (q : Fin 5 → ℕ → ℚ) (ε : ℚ) (k : ℕ) : Option ℚ :=
  runTrial d P.derivativeBound P.table P.input i is q ε k

def boundTrial (P : Program b N) (d : Domain) (i : Fin 3) (is : List (Fin 5))
    (Q : RationalBox 5) (k : ℕ) : Option ℚ :=
  runBoundTrial d P.derivativeBound P.table P.input i is Q k

noncomputable def evaluate (P : Program b N) (d : Domain) (i : Fin 3) (is : List (Fin 5))
    (q : Fin 5 → ℕ → ℚ) (ε : ℚ) : Part ℚ := Nat.rfindOpt (P.valueTrial d i is q ε)

noncomputable def derivativeBounds (P : Program b N) (d : Domain) (i : Fin 3)
    (is : List (Fin 5)) (Q : RationalBox 5) : Part ℚ := Nat.rfindOpt (P.boundTrial d i is Q)

def Represents (P : Program b N) (d : Domain) (F : ℝ → VectorField 3) : Prop :=
  letI := neZeroFive
  (∀ (i : Fin 3) (is : List (Fin 5)) (q : Fin 5 → ℕ → ℚ) (x : Fin 5 → ℝ),
    Names q x → 0 < x 0 → ∀ ε : ℚ, 0 < ε →
      (P.evaluate d i is q ε).Dom ∧
      ∀ r ∈ P.evaluate d i is q ε,
        |mixedD is (forceFunction F i) x-(r:ℝ)| ≤ (ε:ℝ)) ∧
  (∀ (i : Fin 3) (is : List (Fin 5)) (Q : RationalBox 5), 0 < Q.lower 0 →
    (P.derivativeBounds d i is Q).Dom ∧
    ∀ C ∈ P.derivativeBounds d i is Q, 0 ≤ C ∧
      ∀ x ∈ Q.carrier, |mixedD is (forceFunction F i) x| ≤ (C:ℝ))

end VelocityDetection.Effective.MachineRecipe.Program
end

noncomputable section
namespace VelocityDetection.Effective
open Turing

def ComputableReal (x : ℝ) : Prop :=
  ∃ q : ℕ → ℚ, Computable q ∧ ∀ k, |x-(q k:ℝ)| ≤ (accuracy k:ℝ)

end VelocityDetection.Effective
end

noncomputable section
namespace VelocityDetection
open Set Function MeasureTheory Turing
open scoped ContDiff
open Effective Effective.MachineRecipe

theorem main_result :
    ∃ B : ℕ, 0 < B ∧
      (∀ s : ℝ, |deriv (deriv SmoothBump.profile) s| ≤ (B:ℝ)) ∧
    ∀ (ν : ℝ), 0 < ν → ComputableReal ν →
    ∀ (b N : ℕ) [NeZero b] [NeZero N]
      (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)),
    ∃ (Ftor Fcyl : ℝ → VectorField 3),
      (compile B M w).Represents .torus Ftor ∧
      (compile B M w).Represents .cylinder Fcyl ∧
      (ContDiff ℝ ∞ (uncurry (Ftor ν)) ∧
        (∀ t, FactorsThrough (Ftor ν t) PeriodicSpace.cover) ∧
        (∃ K : Set (Coord 2), IsCompact K ∧ (∀ X ∈ K, ∀ i, X i ∈ Ioo (0:ℝ) 1) ∧
          ∀ t X, PeriodicSpace.cover (horizontal X) ∉ PeriodicSpace.cover '' K → Ftor ν t X = 0) ∧
        (∀ T d, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) T, ∀ X,
          ‖iteratedFDeriv ℝ d (uncurry (Ftor ν)) (t,X)‖ ≤ C) ∧
        ∃ u : VectorField 3,
          ContDiff ℝ ∞ (uncurry u) ∧ TorusClass.ComparisonClass u (fun _ _ => 0) ∧
          NavierStokes ν u (fun _ _ => 0) (Ftor ν) ∧
          (Observation.torusEvent u ↔ (TM0.eval M w).Dom) ∧
          ∀ (v : VectorField 3) (p : ScalarField 3), TorusClass.ComparisonClass v p →
            NavierStokes ν v p (Ftor ν) →
            ∀ t ≥ 0, (∀ X, v t X = u t X) ∧ (∀ X, p t X = 0)) ∧
      (ContDiff ℝ ∞ (uncurry (Fcyl ν)) ∧
        UniformDerivatives.Bounded (fun _ : Unit => uncurry (Fcyl ν)) ∧
        (∀ t X z, Fcyl ν t (update X 2 z) = Fcyl ν t X) ∧
        (∀ T : ℝ, ∃ K : Set (Coord 2), IsCompact K ∧ ∀ t ∈ Icc (0:ℝ) T,
          ∀ X : Coord 3, horizontal X ∉ K → Fcyl ν t X = 0) ∧
        ∃ u : VectorField 3,
          ContDiff ℝ ∞ (uncurry u) ∧
          Cylinder.ComparisonClass (fun t x => u t (Cylinder.join x)) (fun _ _ => 0) ∧
          NavierStokes ν u (fun _ _ => 0) (Fcyl ν) ∧
          (∀ t ≥ 0, (∀ x, 0 ≤ u t (Cylinder.join x) 2) ∧
            Integrable (fun x => u t (Cylinder.join x) 2) Cylinder.measure) ∧
          (Observation.planeEvent u ↔ (TM0.eval M w).Dom) ∧
          ∀ (v : VectorField 3) (p : ScalarField 3),
            Cylinder.ComparisonClass (fun t x => v t (Cylinder.join x))
              (fun t x => p t (Cylinder.join x)) →
            NavierStokes ν v p (Fcyl ν) →
            ∀ t ≥ 0, (∀ X, v t X = u t X) ∧ (∀ X, p t X = 0)) := by sorry

end VelocityDetection
end

end OAI
