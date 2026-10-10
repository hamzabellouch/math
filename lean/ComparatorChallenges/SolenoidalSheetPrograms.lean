import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Solenoidal

abbrev Plane := Fin 2 → ℝ
abbrev Space := Fin 3 → ℝ
abbrev SpaceTime := ℝ × Space
abbrev Field := ℝ → Space → Space
abbrev Pressure := ℝ → Space → ℝ
abbrev Torus := Fin 3 → AddCircle (10 : ℝ)

def toTorus (x : Space) : Torus := fun i => (x i : AddCircle (10 : ℝ))

def sheet (y : Plane) : Space := ![y 0, y 1, 2]

structure Rectangle where
  lower : Fin 2 → ℚ
  upper : Fin 2 → ℚ
  positive : ∀ j, lower j < upper j

namespace Rectangle

def carrier (R : Rectangle) : Set Plane :=
  {y | ∀ j, (R.lower j : ℝ) ≤ y j ∧ y j ≤ (R.upper j : ℝ)}

def center (R : Rectangle) : Plane :=
  fun j => ((R.lower j : ℝ) + (R.upper j : ℝ)) / 2

def halfWidth (R : Rectangle) : Plane :=
  fun j => ((R.upper j : ℝ) - (R.lower j : ℝ)) / 2

def inCodingSquare (R : Rectangle) : Prop :=
  ∀ j, 2 ≤ R.lower j ∧ R.upper j ≤ 3

end Rectangle

def SeparatelySeparated {N : ℕ} (R : Fin N → Rectangle) : Prop :=
  ∀ i j, i ≠ j → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ (R i).carrier, ∀ y ∈ (R j).carrier, δ ≤ ‖x - y‖

def diagonalMap (P Q : Rectangle) (r : Fin 2 → ℚ) (y : Plane) : Plane :=
  fun j => Q.center j + (r j : ℝ) * (y j - P.center j)

structure SheetData (N : ℕ) where
  source : Fin N → Rectangle
  target : Fin N → Rectangle
  source_inside : ∀ i, (source i).inCodingSquare
  target_inside : ∀ i, (target i).inCodingSquare
  source_separated : SeparatelySeparated source
  target_separated : SeparatelySeparated target
  ratio : Fin N → Fin 2 → ℚ
  ratio_positive : ∀ i j, 0 < ratio i j
  image_eq : ∀ i,
    diagonalMap (source i) (target i) (ratio i) '' (source i).carrier =
      (target i).carrier

def deck (k : Fin 3 → ℤ) : Space := fun j => 10 * (k j : ℝ)

def SpatiallyPeriodic {E : Type*} (g : ℝ → Space → E) : Prop :=
  ∀ t x k, g t (x + deck k) = g t x

def fundamentalCell : Set Space :=
  Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 10)

def basis (j : Fin 3) : Space := Pi.single j 1

def spatialPartial (u : Field) (j : Fin 3) : Field :=
  fun t x => fderiv ℝ (u t) x (basis j)

def timePartial (u : Field) : Field :=
  fun t x => derivWithin (fun s => u s x) (Set.Ici 0) t

def divergence (u : Field) (t : ℝ) (x : Space) : ℝ :=
  ∑ j : Fin 3, spatialPartial u j t x j

def laplacian (u : Field) : Field :=
  fun t x => ∑ j : Fin 3, spatialPartial (spatialPartial u j) j t x

def advection (u : Field) : Field :=
  fun t x => fderiv ℝ (u t) x (u t x)

def gradient (p : Pressure) : Field :=
  fun t x j => fderiv ℝ (p t) x (basis j)

def DivergenceFree (u : Field) : Prop := ∀ t x, divergence u t x = 0

def MeanZero (u : Field) : Prop :=
  ∀ t, (∫ x in fundamentalCell, u t x) = 0

def Smooth (u : Field) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun z : SpaceTime => u z.1 z.2)

def OnePeriodic (u : Field) : Prop := ∀ t x, u (t + 1) x = u t x

def IntegerCollars (u : Field) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℤ, ∀ t x, |t - (n : ℝ)| < ε → u t x = 0

def cylinder (T : ℝ) : Set SpaceTime := Set.Icc 0 T ×ˢ Set.univ

structure ClassicalSolution (ν : ℝ) (f u : Field) (p : Pressure) : Prop where
  spatial_periodic_u : SpatiallyPeriodic u
  spatial_periodic_p : SpatiallyPeriodic p
  continuous_u : ∀ T, 0 ≤ T →
    ContinuousOn (fun z : SpaceTime => u z.1 z.2) (cylinder T)
  differentiable_t : ∀ t, 0 ≤ t → ∀ x,
    DifferentiableWithinAt ℝ (fun s => u s x) (Set.Ici 0) t
  continuous_t : ∀ T, 0 ≤ T →
    ContinuousOn (fun z : SpaceTime => timePartial u z.1 z.2) (cylinder T)
  differentiable_x : ∀ t, 0 ≤ t → Differentiable ℝ (u t)
  continuous_x : ∀ T, 0 ≤ T → ∀ j,
    ContinuousOn (fun z : SpaceTime => spatialPartial u j z.1 z.2) (cylinder T)
  differentiable_xx : ∀ t, 0 ≤ t → ∀ j,
    Differentiable ℝ (spatialPartial u j t)
  continuous_xx : ∀ T, 0 ≤ T → ∀ i j,
    ContinuousOn (fun z : SpaceTime => spatialPartial (spatialPartial u i) j z.1 z.2)
      (cylinder T)
  continuous_p : ∀ T, 0 ≤ T →
    ContinuousOn (fun z : SpaceTime => p z.1 z.2) (cylinder T)
  differentiable_p : ∀ t, 0 ≤ t → Differentiable ℝ (p t)
  continuous_px : ∀ T, 0 ≤ T →
    ContinuousOn (fun z : SpaceTime => gradient p z.1 z.2) (cylinder T)
  pressure_mean_zero : ∀ t, 0 ≤ t → (∫ x in fundamentalCell, p t x) = 0
  incompressible : ∀ t, 0 ≤ t → ∀ x, divergence u t x = 0
  initial : ∀ x, u 0 x = 0
  equation : ∀ t, 0 ≤ t → ∀ x,
    timePartial u t x + advection u t x =
      -gradient p t x + ν • laplacian u t x + f t x

def MaterialFlow (u : Field) (X : ℝ → Space → Space) : Prop :=
  (∀ a, X 0 a = a) ∧
  (∀ a, ContinuousOn (fun t => X t a) (Set.Ici 0)) ∧
  (∀ a t, 0 ≤ t →
    HasDerivWithinAt (fun s => X s a) (u t (X t a)) (Set.Ici 0) t)

def spacetimeBasis : Fin 4 → SpaceTime :=
  ![(1, 0), (0, basis 0), (0, basis 1), (0, basis 2)]

def mixedDerivative (u : Field) : List (Fin 4) → SpaceTime → Space
  | [] => fun z => u z.1 z.2
  | j :: α => fun z => fderiv ℝ (mixedDerivative u α) z (spacetimeBasis j)

def flatten (z : SpaceTime) : Fin 4 → ℝ := ![z.1, z.2 0, z.2 1, z.2 2]

def NamesReal (c : Nat.Partrec.Code) (r : ℝ) : Prop :=
  ∀ n : ℕ, ∃ q : ℚ, Encodable.encode q ∈ c.eval n ∧
    |(q : ℝ) - r| ≤ (1 / 2 : ℝ) ^ n

def ComputableReal (r : ℝ) : Prop := ∃ c, NamesReal c r

def NamesPoint (c : Nat.Partrec.Code) (z : SpaceTime) : Prop :=
  ∀ n : ℕ, ∃ q : Fin 4 → ℚ,
    @Encodable.encode (Fin 4 → ℚ) Encodable.finArrow q ∈ c.eval n ∧
    ‖(fun j => (q j : ℝ)) - flatten z‖ ≤ (1 / 2 : ℝ) ^ n

def Effective (u : Field) : Prop :=
  ∃ e : Nat.Partrec.Code, ∀ α : List (Fin 4), ∀ c : Nat.Partrec.Code,
    ∀ z : SpaceTime, NamesPoint c z → ∀ ε : ℚ, 0 < ε →
      ∃ q : Fin 3 → ℚ,
        @Encodable.encode (Fin 3 → ℚ) Encodable.finArrow q ∈
          e.eval (Encodable.encode (α, c, ε)) ∧
          ‖(fun j => (q j : ℝ)) - mixedDerivative u α z‖ < (ε : ℝ)

def EffectiveBounds (u : Field) : Prop :=
  ∃ e : Nat.Partrec.Code, ∀ α : List (Fin 4), ∃ B : ℚ,
    Encodable.encode B ∈ e.eval (Encodable.encode α) ∧ 0 ≤ B ∧
      ∀ z : SpaceTime, ‖mixedDerivative u α z‖ ≤ (B : ℝ)

theorem sheet_theorem {N : ℕ} (D : SheetData N) (ν : ℝ)
    (hν : 0 < ν) (hνcomp : ComputableReal ν) :
    ∃ f u : Field, ∃ X : ℝ → Space → Space,
      SpatiallyPeriodic f ∧ SpatiallyPeriodic u ∧
      Smooth f ∧ Smooth u ∧ Effective f ∧
      MeanZero f ∧ DivergenceFree f ∧ OnePeriodic f ∧
      ClassicalSolution ν f u (fun _ _ => 0) ∧
      (∀ v : Field, ∀ p : Pressure, ClassicalSolution ν f v p →
        ∀ t, 0 ≤ t → ∀ x, v t x = u t x ∧ p t x = 0) ∧
      MaterialFlow u X ∧
      (∀ i : Fin N, ∀ y ∈ (D.source i).carrier,
        toTorus (X 1 (sheet y)) =
          toTorus (sheet (diagonalMap (D.source i) (D.target i) (D.ratio i) y))) ∧
      IntegerCollars u ∧ (∀ t x, advection u t x = 0) ∧
      EffectiveBounds f ∧ EffectiveBounds u ∧
      (N = 0 → f = 0 ∧ u = 0) := by
  sorry

end Solenoidal

end

end OAI
