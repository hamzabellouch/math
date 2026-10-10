import Mathlib

namespace OAI

open scoped BigOperators ENNReal Topology
open Set MeasureTheory
namespace RapidForcing

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Field (E : Type) := ℝ → Space → E
abbrev MultiIndex := Fin 3 → ℕ

theorem twoAtLeastTwo : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩

theorem neZeroThree : NeZero 3 := ⟨Nat.succ_ne_zero 2⟩

noncomputable def vec (x y z : ℝ) : Space :=
  letI := twoAtLeastTwo
  WithLp.toLp 2 ![x, y, z]

noncomputable def basis (i : Fin 3) : Space := EuclideanSpace.single i 1

def K : Set Space :=
  letI := twoAtLeastTwo
  letI := neZeroThree
  {x | -2 ≤ x 0 ∧ x 0 ≤ 1 ∧
  -1 ≤ x 1 ∧ x 1 ≤ 2 ∧ -1 ≤ x 2 ∧ x 2 ≤ 1}

noncomputable def spatialD {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (f : Field E) : Field E :=
  fun t x => fderiv ℝ (f t) x (basis i)

noncomputable def timeD {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Field E) : Field E :=
  fun t x => derivWithin (fun s => f s x) (Ici 0) t

noncomputable def spatialMulti {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : MultiIndex) (f : Field E) : Field E :=
  letI := neZeroThree
  (spatialD 0)^[α 0] ((spatialD 1)^[α 1] ((spatialD 2)^[α 2] f))

noncomputable def mixedD {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : ℕ) (α : MultiIndex) (f : Field E) : Field E :=
  timeD^[l] (spatialMulti α f)

def order (α : MultiIndex) : ℕ := ∑ i, α i

def Smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Field E) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) (Ici (0 : ℝ) ×ˢ univ)

def Supported {E : Type} [Zero E] (f : Field E) : Prop :=
  ∀ t : ℝ, 0 ≤ t → tsupport (f t) ⊆ K

def Rapid {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Field E) : Prop :=
  ∀ (J l : ℕ) (α : MultiIndex), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t : ℝ), 0 ≤ t → ∀ x : Space,
      (1 + t) ^ J * ‖mixedD l α f t x‖ ≤ C

def RapidSpaceTime {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Field E) : Prop :=
  ∀ (J l : ℕ) (α : MultiIndex), ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t : ℝ), 0 ≤ t → ∀ x : Space,
      (1 + t + ‖x‖) ^ J * ‖mixedD l α f t x‖ ≤ C

noncomputable def advection (u : Field Space) : Field Space :=
  fun t x => ∑ i, (u t x i) • spatialD i u t x

noncomputable def laplace (u : Field Space) : Field Space :=
  fun t x => ∑ i, spatialD i (spatialD i u) t x

noncomputable def divergence (u : Field Space) : Field ℝ :=
  fun t x => ∑ i, (spatialD i u t x) i

noncomputable def gradient (p : Field ℝ) : Field Space :=
  fun t x => ∑ i, (spatialD i p t x) • basis i

noncomputable def residual (ν : ℝ) (u : Field Space) : Field Space :=
  fun t x => timeD u t x + advection u t x - ν • laplace u t x

def NavierStokes (ν : ℝ) (f u : Field Space) (p : Field ℝ) : Prop :=
  (∀ (t : ℝ), 0 ≤ t → ∀ x : Space,
    timeD u t x + advection u t x =
      -gradient p t x + ν • laplace u t x + f t x) ∧
  (∀ (t : ℝ), 0 ≤ t → ∀ x : Space, divergence u t x = 0) ∧
  (∀ x : Space, u 0 x = 0)

def Classical (u : Field Space) (p : Field ℝ) : Prop :=
  letI := twoAtLeastTwo
  (∀ t : ℝ, 0 ≤ t → ContDiff ℝ 2 (u t) ∧ ContDiff ℝ 1 (p t)) ∧
  (∀ x : Space, DifferentiableOn ℝ (fun t => u t x) (Ici 0)) ∧
  ∀ T : ℝ, 0 ≤ T →
    let cylinder := Icc (0 : ℝ) T ×ˢ (univ : Set Space)
    ContinuousOn (Function.uncurry u) cylinder ∧
    ContinuousOn (Function.uncurry (timeD u)) cylinder ∧
    (∀ i, ContinuousOn (Function.uncurry (spatialD i u)) cylinder) ∧
    (∀ i j, ContinuousOn (Function.uncurry (spatialD i (spatialD j u))) cylinder) ∧
    ContinuousOn (Function.uncurry p) cylinder ∧
    (∀ i, ContinuousOn (Function.uncurry (spatialD i p)) cylinder)

def L2ContinuousOn {E : Type} [NormedAddCommGroup E]
    (f : Field E) (T : ℝ) : Prop :=
  letI := twoAtLeastTwo
  ∃ v : ℝ → Lp E 2 (volume : Measure Space),
    ContinuousOn v (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, (v t : Space → E) =ᵐ[volume] f t

def L2C1On (u : Field Space) (T : ℝ) : Prop :=
  letI := twoAtLeastTwo
  ∃ v v' : ℝ → Lp Space 2 (volume : Measure Space),
    ContinuousOn v (Icc 0 T) ∧ ContinuousOn v' (Icc 0 T) ∧
    (∀ t ∈ Icc 0 T, (v t : Space → Space) =ᵐ[volume] u t) ∧
    (∀ t ∈ Icc 0 T, (v' t : Space → Space) =ᵐ[volume] timeD u t) ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt v (v' t) (Icc 0 T) t

def EnergyRegularity (u : Field Space) (p : Field ℝ) : Prop :=
  ∀ T : ℝ, 0 ≤ T →
    (∀ α : MultiIndex, order α ≤ 2 → L2ContinuousOn (spatialMulti α u) T) ∧
    L2C1On u T ∧
    (∀ α : MultiIndex, order α ≤ 1 → L2ContinuousOn (spatialMulti α p) T)

def EnergyClass (u : Field Space) (p : Field ℝ) : Prop :=
  EnergyRegularity u p ∧
  ∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, ∀ t ∈ Icc 0 T, ∀ x : Space,
    ‖u t x‖ + ‖fderiv ℝ (u t) x‖ ≤ C

def EnergyCompetitor (u : Field Space) (p : Field ℝ) : Prop :=
  EnergyRegularity u p ∧
  ∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, ∀ t ∈ Icc 0 T, ∀ x : Space, ‖u t x‖ ≤ C

def UniqueEnergySolution (ν : ℝ) (f u : Field Space) (p : Field ℝ) : Prop :=
  Classical u p ∧ EnergyClass u p ∧ NavierStokes ν f u p ∧
  ∀ (v : Field Space) (q : Field ℝ),
    Classical v q → EnergyCompetitor v q → NavierStokes ν f v q →
    ∀ (t : ℝ), 0 ≤ t → ∀ x : Space, v t x = u t x ∧ q t x = p t x

def TrajectoryOn (u : Field Space) (a : Space) (T : ℝ) (γ : ℝ → Space) : Prop :=
  γ 0 = a ∧ ∀ t ∈ Icc 0 T,
    HasDerivWithinAt γ (u t (γ t)) (Icc 0 T) t

def MaterialFlow (u : Field Space) (X : ℝ → Space → Space) : Prop :=
  (∀ a : Space, X 0 a = a) ∧
  (∀ (a : Space) (t : ℝ), 0 ≤ t →
    HasDerivWithinAt (fun s => X s a) (u t (X t a)) (Ici 0) t) ∧
  (∀ (T : ℝ), 0 < T → ∀ (a : Space) (γ : ℝ → Space),
    TrajectoryOn u a T γ → ∀ t ∈ Icc 0 T, γ t = X t a)

abbrev Move := Fin 3

structure Machine where
  states : ℕ
  symbols : ℕ
  states_pos : 0 < states
  symbols_pos : 0 < symbols
  initial : Fin states
  transition : Fin states → Fin symbols → Option (Fin states × Fin symbols × Move)

namespace Machine

abbrev Input (M : Machine) := List (Fin M.symbols)

def blank (M : Machine) : Fin M.symbols := ⟨0, M.symbols_pos⟩

def description (M : Machine) : ℕ × ℕ × ℕ × List (Option (ℕ × ℕ × Move)) :=
  (M.states, M.symbols, M.initial.val,
    (List.finRange M.states).flatMap fun q =>
      (List.finRange M.symbols).map fun z =>
        (M.transition q z).map fun v => (v.1.val, v.2.1.val, v.2.2))

def inputDescription (M : Machine) (w : M.Input) : ℕ :=
  Encodable.encode (M.description, w.map Fin.val)

structure Config (M : Machine) where
  state : Fin (M.states + 1)
  head : ℤ
  tape : ℤ → Fin M.symbols

def initialConfig (M : Machine) (w : M.Input) : M.Config :=
  ⟨⟨M.initial.val, Nat.lt_succ_of_lt M.initial.isLt⟩, 0,
    fun i => if 0 ≤ i then w[i.toNat]?.getD M.blank else M.blank⟩

def nextConfig (M : Machine) (c : M.Config) : M.Config :=
  if h : c.state.val < M.states then
    match M.transition ⟨c.state.val, h⟩ (c.tape c.head) with
    | none => ⟨⟨M.states, Nat.lt_succ_self _⟩, c.head, c.tape⟩
    | some (q', z', d) =>
      ⟨⟨q'.val, Nat.lt_succ_of_lt q'.isLt⟩, c.head + (d.val : ℤ) - 1,
        Function.update c.tape c.head z'⟩
  else c

def run (M : Machine) (w : M.Input) (n : ℕ) : M.Config :=
  M.nextConfig^[n] (M.initialConfig w)

def Halts (M : Machine) (w : M.Input) : Prop :=
  ∃ n : ℕ, (M.run w n).state.val = M.states

end Machine

structure ScaleData where
  rA : ℕ
  rQ : ℕ
  B : ℕ

namespace ScaleData

def A (d : ScaleData) : ℕ := 2 ^ d.rA
def S (d : ScaleData) : ℕ := 2 ^ d.rQ
def P (_d : ScaleData) (n : ℕ) : ℕ := 2 ^ (n + 2)
def L (d : ScaleData) (n : ℕ) : ℕ := d.rQ + n + 2 + d.rA * (2 * n + d.B + 1)
def capacity (d : ScaleData) (n : ℕ) : ℕ := 2 ^ d.L n
def C (d : ScaleData) : ℕ := max 1 (max (d.L 0) (1 + 2 * d.rA))
def s (d : ScaleData) (n : ℕ) : ℕ := d.C * 2 ^ ((n + 2) ^ 2)
def D (d : ScaleData) (n : ℕ) : ℕ := 2 ^ d.s n
noncomputable def δ (d : ScaleData) (n : ℕ) : ℝ :=
  letI := twoAtLeastTwo
  (1 / 2 : ℝ) ^ d.s n
noncomputable def b (d : ScaleData) (n : ℕ) : ℝ := d.δ (n + 1) * (d.capacity (n + 1) : ℝ)

end ScaleData

namespace Machine

def scaleData (M : Machine) (w : M.Input) : ScaleData :=
  ⟨M.symbols + 1, M.states + 1, w.length⟩

def instruction (M : Machine) (q z : ℕ) : ℕ × ℕ × Move :=
  letI := neZeroThree
  if hq : q < M.states then
    if hz : z < M.symbols then
      match M.transition ⟨q, hq⟩ ⟨z, hz⟩ with
      | none => (M.states, z, 1)
      | some (q', z', d) => (q'.val, z'.val, d)
    else (M.states, z, 1)
  else (M.states, z, 1)

def terminalDigit (M : Machine) (d : ScaleData) (k : ℕ) : ℕ :=
  if k % d.S = M.states then 1 else 0

def nextDigit (M : Machine) (d : ScaleData) (n k : ℕ) : ℕ :=
  let q := k % d.S
  let j := (k / d.S) % d.P n
  let T := k / (d.S * d.P n)
  let z := (T / d.A ^ j) % d.A
  if q < M.states ∧ j ≤ 2 * n ∧ z < M.symbols then
    let inst := M.instruction q z
    inst.1 + d.S * (j + inst.2.2.val +
      d.P (n + 1) * d.A * (T - z * d.A ^ j + inst.2.1 * d.A ^ j))
  else 0

def initialDigit (M : Machine) (w : M.Input) : ℕ :=
  let d := M.scaleData w
  M.initial.val + d.S * (d.P 0 *
    ((w.map Fin.val).zipIdx.map fun a => a.1 * d.A ^ a.2).sum)

end Machine

noncomputable def θ (t : ℝ) : ℝ :=
  letI := twoAtLeastTwo
  Real.smoothTransition (2 * t - 1 / 2)

noncomputable def ζ (v : Space) : ℝ :=
  ∏ i, Real.smoothTransition (16 * (v i + 1 / 8)) *
    Real.smoothTransition (16 * (1 / 8 - v i))

noncomputable def cross (a b : Space) : Space :=
  letI := neZeroThree
  vec (a 1 * b 2 - a 2 * b 1) (a 2 * b 0 - a 0 * b 2) (a 0 * b 1 - a 1 * b 0)

noncomputable def curl (v : Space → Space) (x : Space) : Space :=
  letI := neZeroThree
  vec ((fderiv ℝ v x (basis 1)) 2 - (fderiv ℝ v x (basis 2)) 1)
    ((fderiv ℝ v x (basis 2)) 0 - (fderiv ℝ v x (basis 0)) 2)
    ((fderiv ℝ v x (basis 0)) 1 - (fderiv ℝ v x (basis 1)) 0)

noncomputable def movingCurl (c : ℝ → Space) (δ : ℝ) : Field Space :=
  letI := twoAtLeastTwo
  fun σ x => curl (fun y =>
    ζ (δ⁻¹ • (y - c σ)) • ((1 / 2 : ℝ) • cross (deriv c σ) (y - c σ))) x

noncomputable def addressCenter (d : ScaleData) (n m : ℕ) : Space :=
  vec (-1) ((m : ℝ) * d.δ n) 0

noncomputable def addressDisplacement (M : Machine) (d : ScaleData) (n m : ℕ) : Space :=
  let k := m % d.capacity n
  vec (-d.b n * (M.terminalDigit d k : ℝ))
    (d.δ (n + 1) * (M.nextDigit d n k : ℝ)) 0

noncomputable def addressPath (M : Machine) (d : ScaleData) (n m : ℕ) (σ : ℝ) : Space :=
  addressCenter d n m + θ σ • addressDisplacement M d n m

noncomputable def addressedVelocity (M : Machine) (w : M.Input) : Field Space :=
  let d := M.scaleData w
  let y₀ := d.δ 0 * (M.initialDigit w : ℝ)
  fun t x => if t ≤ 1 then
    movingCurl (fun s => θ s • vec (-1) y₀ 0) 1 t x
  else
    let n := Nat.floor (t - 1)
    ∑ m ∈ Finset.range (d.D n + 1),
      movingCurl (addressPath M d n m) (d.δ n) (t - 1 - (n : ℝ)) x

noncomputable def addressedForce (ν : ℝ) (M : Machine) (w : M.Input) : Field Space :=
  residual ν (addressedVelocity M w)

abbrev Program := Nat.Partrec.Code
abbrev RationalVector := ℚ × ℚ × ℚ
abbrev RationalPoint := ℚ × RationalVector

noncomputable def rationalVector (q : RationalVector) : Space :=
  vec q.1 q.2.1 q.2.2

noncomputable def accuracy (n : ℕ) : ℝ :=
  letI := twoAtLeastTwo
  (1 / 2 : ℝ) ^ n

def NamesReal (c : Program) (x : ℝ) : Prop :=
  ∀ n : ℕ, ∃ q : ℚ, Encodable.encode q ∈ c.eval n ∧ |(q : ℝ) - x| ≤ accuracy n

def ComputableReal (x : ℝ) : Prop := ∃ c : Program, NamesReal c x

def NamesPoint (c : Program) (t : ℝ) (x : Space) : Prop :=
  ∀ n : ℕ, ∃ q : RationalPoint, Encodable.encode q ∈ c.eval n ∧
    |(q.1 : ℝ) - t| ≤ accuracy n ∧ ‖rationalVector q.2 - x‖ ≤ accuracy n

def evalQuery (l : ℕ) (α : MultiIndex) (name : Program) (precision : ℕ) : ℕ :=
  letI := neZeroThree
  Encodable.encode (l, α 0, α 1, α 2, Encodable.encode name, precision)

def boundQuery (J l : ℕ) (α : MultiIndex) : ℕ :=
  letI := neZeroThree
  Encodable.encode (J, l, α 0, α 1, α 2)

def EvaluatesMixed (c : Program) (f : Field Space) : Prop :=
  ∀ (l : ℕ) (α : MultiIndex) (name : Program) (t : ℝ) (x : Space),
    0 ≤ t → NamesPoint name t x → ∀ n : ℕ, ∃ q : RationalVector,
      Encodable.encode q ∈ c.eval (evalQuery l α name n) ∧
      ‖rationalVector q - mixedD l α f t x‖ ≤ accuracy n

def BoundsMixed (c : Program) (f : Field Space) : Prop :=
  ∀ (J l : ℕ) (α : MultiIndex), ∃ C : ℕ,
    C ∈ c.eval (boundQuery J l α) ∧
    ∀ (t : ℝ), 0 ≤ t → ∀ x : Space,
      (1 + t + ‖x‖) ^ J * ‖mixedD l α f t x‖ ≤ (C : ℝ)

def ForceProgram (codes : ℕ × ℕ) (f : Field Space) : Prop :=
  EvaluatesMixed (Nat.Partrec.Code.ofNatCode codes.1) f ∧
  BoundsMixed (Nat.Partrec.Code.ofNatCode codes.2) f

end RapidForcing

end OAI
