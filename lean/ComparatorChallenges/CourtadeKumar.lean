import Mathlib

namespace OAI

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

abbrev Cube (n : ℕ) := Fin n → Bool

end LeanBlast.GotsmanLinial

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

abbrev Cube (n : ℕ) := LeanBlast.GotsmanLinial.Cube n

def cubeAverage {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  (∑ x, g x) / (2 : ℝ) ^ n

def ell : ℝ := Real.log 2

def bitFlipKernel {n : ℕ} (ε : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then 1 - ε else ε

def jointProbability {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (b : Bool) (y : Cube n) : ℝ :=
  cubeAverage (fun x => if f x = b then bitFlipKernel ε x y else 0)

def functionMarginal {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (b : Bool) : ℝ :=
  ∑ y, jointProbability ε f b y

def observationMarginal {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (y : Cube n) : ℝ :=
  ∑ b : Bool, jointProbability ε f b y

def xlogx (t : ℝ) : ℝ := t * Real.log t

def binaryEntropy (ε : ℝ) : ℝ :=
  -(xlogx ε + xlogx (1 - ε)) / ell

def mutualInformation {n : ℕ} (ε : ℝ) (f : Cube n → Bool) : ℝ :=
  (∑ b : Bool, ∑ y : Cube n,
    if 0 < jointProbability ε f b y then
      jointProbability ε f b y *
        Real.log (jointProbability ε f b y /
          (functionMarginal ε f b * observationMarginal ε f y))
    else 0) / ell

def dictator {n : ℕ} (i : Fin n) (x : Cube n) : Bool := x i

def complementDictator {n : ℕ} (i : Fin n) (x : Cube n) : Bool := !(x i)

def CourtadeKumarStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ (1 : ℝ) / 2 →
      ∀ f : Cube n → Bool, mutualInformation ε f ≤ 1 - binaryEntropy ε

def DictatorAttainmentStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ (1 : ℝ) / 2 →
      ∀ i : Fin n,
        mutualInformation ε (dictator i) = 1 - binaryEntropy ε ∧
        mutualInformation ε (complementDictator i) = 1 - binaryEntropy ε

def FullStatement : Prop := CourtadeKumarStatement ∧ DictatorAttainmentStatement

theorem courtadeKumarAndAttainment : FullStatement := by
  sorry

end LeanBlast.CourtadeKumar

end

end OAI
