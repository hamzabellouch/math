import Mathlib

namespace OAI

open scoped BigOperators ContDiff

namespace BoxTransport.Routing

abbrev Space := Fin 3 → ℝ
abbrev RationalSpace := Fin 3 → ℚ
abbrev SpaceTime := ℝ × Space
abbrev RationalSpaceTime := ℚ × RationalSpace
abbrev Field := SpaceTime → Space

abbrev Axis := Option (Fin 3)

def coordinateVector (j : Fin 3) : Space := Pi.single j 1

def coordinateDirection : Axis → SpaceTime
  | none => (1, 0)
  | some j => (0, coordinateVector j)

def realPoint (q : RationalSpace) : Space := fun j => (q j : ℝ)

def realSpaceTime (q : RationalSpaceTime) : SpaceTime := (q.1, realPoint q.2)

def realBox (c r : Space) : Set Space :=
  {x | ∀ j, |x j - c j| ≤ r j}

def solidBox (a h : RationalSpace) : Set Space :=
  realBox (realPoint a) (realPoint h)

def prescribedAffine (a b h k : RationalSpace) (x : Space) : Space :=
  fun j => (b j : ℝ) + ((k j / h j : ℚ) : ℝ) * (x j - (a j : ℝ))

noncomputable def mixedDerivative : List Axis → Field → Field
  | [], U => U
  | j :: js, U => fun p => fderiv ℝ (mixedDerivative js U) p (coordinateDirection j)

abbrev RationalCode := ℕ × ℕ × ℕ

def rationalValue (q : RationalCode) : ℚ := ((q.1 : ℚ) - q.2.1) / (q.2.2 + 1)

abbrev RationalPointCode := RationalCode × RationalCode × RationalCode × RationalCode

def codeSpaceTime (q : RationalPointCode) : SpaceTime :=
  ((rationalValue q.1 : ℝ), ![(rationalValue q.2.1 : ℝ),
    (rationalValue q.2.2.1 : ℝ), (rationalValue q.2.2.2 : ℝ)])

abbrev EvaluationRequest := List Axis × RationalPointCode × ℕ × Fin 3

def Effective (U : Field) : Prop :=
  ∃ eval : EvaluationRequest → RationalCode,
    ∃ modulus : List Axis × ℕ → ℕ,
      ∃ bound : List Axis → ℕ,
        Computable eval ∧ Computable modulus ∧ Computable bound ∧
        (∀ (ds : List Axis) (q : RationalPointCode) (n : ℕ) (p : SpaceTime),
          ‖p - codeSpaceTime q‖ ≤ ((modulus (ds, n) : ℝ) + 1)⁻¹ →
          ∀ j : Fin 3,
            |mixedDerivative ds U p j - (rationalValue (eval (ds, q, n, j)) : ℝ)| ≤
              ((n : ℝ) + 1)⁻¹) ∧
        (∀ (ds : List Axis) (p : SpaceTime) (j : Fin 3),
          |mixedDerivative ds U p j| ≤ (bound ds : ℝ))

noncomputable def spatialDivergence (U : Field) (t : ℝ) (x : Space) : ℝ :=
  ∑ j : Fin 3, (fderiv ℝ (fun y => U (t, y)) x (coordinateVector j)) j

def AdmissibleField (U : Field) : Prop :=
  ContDiff ℝ ∞ U ∧ HasCompactSupport U ∧ Effective U ∧
    (∀ t x, spatialDivergence U t x = 0) ∧
    (∀ (t : ℝ) (x : Space), t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → U (t, x) = 0)

def IsGlobalFlow (U : Field) (Φ : ℝ → Space → Space) : Prop :=
  (∀ x, Φ 0 x = x) ∧
    (∀ t x, HasDerivAt (fun s => Φ s x) (U (t, Φ t x)) t) ∧
    (∀ (x : Space) (γ : ℝ → Space), γ 0 = x →
      (∀ t, HasDerivAt γ (U (t, γ t)) t) → ∀ t, γ t = Φ t x)

def Delivers {n : ℕ} (a b h k : Fin n → RationalSpace)
    (Φ : ℝ → Space → Space) : Prop :=
  ∀ i, ∃ O : Set Space, IsOpen O ∧ solidBox (a i) (h i) ⊆ O ∧
    ∀ x ∈ O, Φ 1 x = prescribedAffine (a i) (b i) (h i) (k i) x

theorem balanced_box_routing
    (n : ℕ) (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (ha : Pairwise fun i j => Disjoint (solidBox (a i) (h i)) (solidBox (a j) (h j)))
    (hb : Pairwise fun i j => Disjoint (solidBox (b i) (k i)) (solidBox (b j) (k j)))
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1) :
    ∃ U : Field, ∃ Φ : ℝ → Space → Space,
      AdmissibleField U ∧ IsGlobalFlow U Φ ∧ Delivers a b h k Φ := by
  sorry

end BoxTransport.Routing

end OAI
