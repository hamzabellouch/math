import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

namespace ShearFlows

theorem neZeroTwo : NeZero 2 := ⟨Nat.succ_ne_zero 1⟩

theorem neZeroThree : NeZero 3 := ⟨Nat.succ_ne_zero 2⟩

theorem neZeroFour : NeZero 4 := ⟨Nat.succ_ne_zero 3⟩

theorem neZeroEight : NeZero 8 := ⟨Nat.succ_ne_zero 7⟩

theorem twoAtLeastTwo : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩

theorem fourAtLeastTwo : Nat.AtLeastTwo 4 := ⟨by decide⟩
theorem fiveAtLeastTwo : Nat.AtLeastTwo 5 := ⟨by decide⟩

theorem eightAtLeastTwo : Nat.AtLeastTwo 8 := ⟨by decide⟩

theorem sixteenAtLeastTwo : Nat.AtLeastTwo 16 := ⟨by decide⟩

theorem thirtyTwoAtLeastTwo : Nat.AtLeastTwo 32 := ⟨by decide⟩

theorem oneTwentyEightAtLeastTwo : Nat.AtLeastTwo 128 := ⟨by decide⟩

abbrev Plane := Fin 2 → ℝ
abbrev Space := Fin 3 → ℝ
abbrev SpaceTime := ℝ × Space
abbrev Velocity := SpaceTime → Space
abbrev Pressure := SpaceTime → ℝ

structure RationalBox (n : ℕ) where
  lower : Fin n → ℚ
  upper : Fin n → ℚ

namespace RationalBox

def encoding (n : ℕ) : RationalBox n ≃ ((Fin n → ℚ) × (Fin n → ℚ)) where
  toFun B := (B.lower, B.upper)
  invFun B := ⟨B.1, B.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (n : ℕ) : Primcodable (RationalBox n) :=
  Primcodable.ofEquiv _ (encoding n)

def carrier {n : ℕ} (B : RationalBox n) : Set (Fin n → ℝ) :=
  {x | ∀ j, (B.lower j : ℝ) ≤ x j ∧ x j ≤ (B.upper j : ℝ)}

def center {n : ℕ} (B : RationalBox n) : Fin n → ℝ :=
  fun j => ((B.lower j : ℝ) + (B.upper j : ℝ)) / 2

def halfWidth {n : ℕ} (B : RationalBox n) (j : Fin n) : ℝ :=
  ((B.upper j : ℝ) - (B.lower j : ℝ)) / 2

def positive {n : ℕ} (B : RationalBox n) : Prop :=
  ∀ j, B.lower j < B.upper j

def nonemptyBox {n : ℕ} (B : RationalBox n) : Prop :=
  ∀ j, B.lower j ≤ B.upper j

end RationalBox

structure Instruction where
  source : RationalBox 2
  target : RationalBox 2
  factor : ℚ

namespace Instruction

def encoding : Instruction ≃ (RationalBox 2 × RationalBox 2 × ℚ) where
  toFun b := (b.source, b.target, b.factor)
  invFun b := ⟨b.1, b.2.1, b.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Instruction := Primcodable.ofEquiv _ encoding

def affine (b : Instruction) (x : Plane) : Plane :=
  ![b.target.center 0 + (b.factor : ℝ) * (x 0 - b.source.center 0),
    b.target.center 1 + (x 1 - b.source.center 1) / (b.factor : ℝ)]

end Instruction

structure Input where
  period : ℚ
  chart : RationalBox 3
  h : ℚ
  codingHeight : ℚ
  centers : RationalBox 2
  instructions : List Instruction

namespace Input

def encoding : Input ≃
    (ℚ × RationalBox 3 × ℚ × ℚ × RationalBox 2 × List Instruction) where
  toFun d := (d.period, d.chart, d.h, d.codingHeight, d.centers, d.instructions)
  invFun d := ⟨d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2.1, d.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Input := Primcodable.ofEquiv _ encoding

def inChart (d : Input) (x : Space) : Prop :=
  ∀ j, (d.chart.lower j : ℝ) < x j ∧ x j < (d.chart.upper j : ℝ)

def inPlanarChart (d : Input) (x : Plane) : Prop :=
  ∀ j, (d.chart.lower j.castSucc : ℝ) < x j ∧
    x j < (d.chart.upper j.castSucc : ℝ)

end Input

def PositivelySeparated (A B : Set Plane) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ A, ∀ y ∈ B, ε ≤ ‖x - y‖

structure ValidInput (d : Input) : Prop where
  period_pos : 0 < d.period
  chart_positive : d.chart.positive
  chart_length : ∀ j, d.chart.upper j - d.chart.lower j < d.period
  h_pos : 0 < d.h
  centers_nonempty : d.centers.nonemptyBox
  chartMargin : ∀ j : Fin 2,
    (d.chart.lower j.castSucc : ℝ) < (d.centers.lower j : ℝ) - 2 * (d.h : ℝ) ∧
    (d.centers.upper j : ℝ) + 2 * (d.h : ℝ) < (d.chart.upper j.castSucc : ℝ)
  height_inside : (d.chart.lower 2 : ℝ) < (d.codingHeight : ℝ) ∧
    (d.codingHeight : ℝ) < (d.chart.upper 2 : ℝ)
  source_positive : ∀ b ∈ d.instructions, b.source.positive
  target_positive : ∀ b ∈ d.instructions, b.target.positive
  source_in_chart : ∀ b ∈ d.instructions, b.source.carrier ⊆ d.inPlanarChart
  target_in_chart : ∀ b ∈ d.instructions, b.target.carrier ⊆ d.inPlanarChart
  factor_pos : ∀ b ∈ d.instructions, 0 < b.factor
  image_eq : ∀ b ∈ d.instructions, b.affine '' b.source.carrier = b.target.carrier
  source_separation : ∀ i j : Fin d.instructions.length, i ≠ j →
    PositivelySeparated (d.instructions[i].source.carrier)
      (d.instructions[j].source.carrier)
  target_separation : ∀ i j : Fin d.instructions.length, i ≠ j →
    PositivelySeparated (d.instructions[i].target.carrier)
      (d.instructions[j].target.carrier)
  halfWidths : ∀ b ∈ d.instructions, ∀ j,
    b.source.halfWidth j ≤ (d.h : ℝ) ∧ b.target.halfWidth j ≤ (d.h : ℝ)
  source_centers : ∀ b ∈ d.instructions, b.source.center ∈ d.centers.carrier
  target_centers : ∀ b ∈ d.instructions, b.target.center ∈ d.centers.carrier

def basis (j : Fin 3) : Space := Pi.single j 1

def horizontal (x : Space) : Plane := ![x 0, x 1]

def atHeight (x : Plane) (z : ℝ) : Space := ![x 0, x 1, z]

def latticeVector (L : ℝ) (n : Fin 3 → ℤ) : Space := fun j => L * (n j : ℝ)

def SpatiallyPeriodic {E : Type*} (L : ℝ) (g : SpaceTime → E) : Prop :=
  ∀ t x n, g (t, x + latticeVector L n) = g (t, x)

def TimePeriodic {E : Type*} (g : SpaceTime → E) : Prop :=
  ∀ t x, g (t + 1, x) = g (t, x)

def fundamentalCube (L : ℝ) : Set Space := Icc 0 (fun _ => L)

def derivative (U : Space → Space) (j : Fin 3) (x : Space) : Space :=
  fderiv ℝ U x (basis j)

def divergence (U : Space → Space) (x : Space) : ℝ :=
  ∑ j, derivative U j x j

def laplacian (U : Space → Space) (x : Space) : Space :=
  ∑ j, fderiv ℝ (derivative U j) x (basis j)

def advection (U : Space → Space) (x : Space) : Space :=
  fderiv ℝ U x (U x)

def gradient (p : Space → ℝ) (x : Space) : Space :=
  fun j => fderiv ℝ p x (basis j)

def HasZeroMean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ) (g : SpaceTime → E) : Prop :=
  ∀ t, (∫ x in fundamentalCube L, g (t, x)) = 0

def Solenoidal (V : Velocity) : Prop :=
  ∀ t x, divergence (fun y => V (t, y)) x = 0

def ZeroAdvection (V : Velocity) : Prop :=
  ∀ t x, advection (fun y => V (t, y)) x = 0

def timeDerivative (V : Velocity) (t : ℝ) (x : Space) : Space :=
  deriv (fun s => V (s, x)) t

def force (ν : ℝ) (V : Velocity) : Velocity :=
  fun y => timeDerivative V y.1 y.2 - ν • laplacian (fun x => V (y.1, x)) y.2

def spaceTimeDirection (j : Fin 4) : SpaceTime :=
  Fin.cases (1, 0) (fun k => (0, basis k)) j

def mixedDerivative (V : Velocity) : List (Fin 4) → Velocity
  | [] => V
  | j :: α => fun y => fderiv ℝ (mixedDerivative V α) y (spaceTimeDirection j)

def BoundedMixedDerivatives (V : Velocity) : Prop :=
  ∀ α, ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖mixedDerivative V α y‖ ≤ B

def rationalPoint (q : ℚ × (Fin 3 → ℚ)) : SpaceTime :=
  ((q.1 : ℝ), fun j => (q.2 j : ℝ))

def errorTolerance (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

def ComputableReal (r : ℝ) : Prop :=
  ∃ code : Nat.Partrec.Code, ∀ n : ℕ, ∃ q : ℚ,
    Encodable.encode q ∈ code.eval n ∧ |r - (q : ℝ)| ≤ errorTolerance n

structure Schedule where
  start : Fin 7 → ℚ
  finish : Fin 7 → ℚ
  intervals : ∀ j, 0 < start j ∧ start j < finish j ∧ finish j < 1
  ordered : ∀ i j, i < j → finish i < start j
  progress : Fin 7 → ℝ → ℝ
  smooth : ∀ j, ContDiff ℝ ∞ (progress j)
  monotone : ∀ j, Monotone (progress j)
  range : ∀ j t, progress j t ∈ Icc (0 : ℝ) 1
  before : ∀ j t, t ≤ (start j : ℝ) → progress j t = 0
  after : ∀ j t, (finish j : ℝ) ≤ t → progress j t = 1

structure IsMaterialFlow (L : ℝ) (V : Velocity) (Φ : ℝ → Space → Space) : Prop where
  initial : ∀ a, Φ 0 a = a
  ode : ∀ t a, HasDerivAt (fun s => Φ s a) (V (t, Φ t a)) t
  equivariant : ∀ t a n,
    Φ t (a + latticeVector L n) = Φ t a + latticeVector L n
  unique : ∀ a (γ : ℝ → Space), γ 0 = a →
    (∀ t, HasDerivAt γ (V (t, γ t)) t) → ∀ t, γ t = Φ t a

def sourceTube (b : Instruction) (z δ : ℝ) : Set Space :=
  {x | ∃ y ∈ b.source.carrier, ‖horizontal x - y‖ < δ ∧ |x 2 - z| < δ}

def scaledOffset (b : Instruction) (x : Plane) : Plane :=
  ![(b.factor : ℝ) * (x 0 - b.source.center 0),
    (x 1 - b.source.center 1) / (b.factor : ℝ)]

structure StageMotion (d : Input) (Φ : ℝ → Space → Space) (s : Schedule) : Prop where
  lift : ∀ b ∈ d.instructions, ∀ X ∈ b.source.carrier,
    ∀ t ∈ Icc (0 : ℝ) (s.finish 0 : ℝ),
      horizontal (Φ t (atHeight X d.codingHeight)) = X
  scaling : ∀ b ∈ d.instructions, ∀ X ∈ b.source.carrier,
    ∀ t ∈ Icc (s.start 1 : ℝ) (s.finish 4 : ℝ),
      ‖horizontal (Φ t (atHeight X d.codingHeight)) - b.source.center‖ ≤ 2 * (d.h : ℝ)
  translation_offset : ∀ b ∈ d.instructions, ∀ X ∈ b.source.carrier,
    ‖scaledOffset b X‖ ≤ (d.h : ℝ)
  translation : ∀ b ∈ d.instructions, ∀ X ∈ b.source.carrier,
    ∀ t ∈ Icc (s.start 5 : ℝ) (s.finish 5 : ℝ),
      horizontal (Φ t (atHeight X d.codingHeight)) =
        (1 - s.progress 5 t) • b.source.center +
          s.progress 5 t • b.target.center + scaledOffset b X
  lower : ∀ b ∈ d.instructions, ∀ X ∈ b.source.carrier,
    ∀ t ∈ Icc (s.start 6 : ℝ) 1,
      horizontal (Φ t (atHeight X d.codingHeight)) = b.affine X

def initialTimeDerivative (u : Velocity) (t : ℝ) (x : Space) : Space :=
  derivWithin (fun s => u (s, x)) (Ici 0) t

def timeCylinder (T : ℝ) : Set SpaceTime := Icc (0 : ℝ) T ×ˢ univ

structure ClassicalRegularity (u : Velocity) (p : Pressure) : Prop where
  spatial_u : ∀ t, 0 ≤ t → ContDiff ℝ 2 (fun x => u (t, x))
  temporal_u : ∀ t, 0 ≤ t → ∀ x,
    DifferentiableWithinAt ℝ (fun s => u (s, x)) (Ici 0) t
  spatial_p : ∀ t, 0 ≤ t → ContDiff ℝ 1 (fun x => p (t, x))
  continuous_u : ∀ T, 0 ≤ T → ContinuousOn u (timeCylinder T)
  continuous_du : ∀ T, 0 ≤ T → ContinuousOn
    (fun y : SpaceTime => fderiv ℝ (fun x => u (y.1, x)) y.2) (timeCylinder T)
  continuous_ddu : ∀ T, 0 ≤ T → ContinuousOn
    (fun y : SpaceTime => fderiv ℝ (fderiv ℝ (fun x => u (y.1, x))) y.2)
    (timeCylinder T)
  continuous_ut : ∀ T, 0 ≤ T → ContinuousOn
    (fun y : SpaceTime => initialTimeDerivative u y.1 y.2) (timeCylinder T)
  continuous_p : ∀ T, 0 ≤ T → ContinuousOn p (timeCylinder T)
  continuous_dp : ∀ T, 0 ≤ T → ContinuousOn
    (fun y : SpaceTime => gradient (fun x => p (y.1, x)) y.2) (timeCylinder T)

structure IsClassicalSolution (L ν : ℝ) (f u : Velocity) (p : Pressure) : Prop where
  regularity : ClassicalRegularity u p
  periodic_u : ∀ t, 0 ≤ t → ∀ x n, u (t, x + latticeVector L n) = u (t, x)
  periodic_p : ∀ t, 0 ≤ t → ∀ x n, p (t, x + latticeVector L n) = p (t, x)
  pressure_mean : ∀ t, 0 ≤ t → (∫ x in fundamentalCube L, p (t, x)) = 0
  initial : ∀ x, u (0, x) = 0
  divergence_zero : ∀ t, 0 ≤ t → ∀ x, divergence (fun y => u (t, y)) x = 0
  equation : ∀ t, 0 ≤ t → ∀ x,
    initialTimeDerivative u t x + advection (fun y => u (t, y)) x =
      -gradient (fun y => p (t, y)) x +
        ν • laplacian (fun y => u (t, y)) x + f (t, x)

def kineticEnergy (L : ℝ) (u : Velocity) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in fundamentalCube L, ∑ j : Fin 3, (u (t, x) j) ^ 2

end ShearFlows

end

end OAI
