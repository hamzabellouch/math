import OAI.InformationTheory.BooleanNoise.Model
import OAI.Combinatorics.GotsmanLinial.Statement
import Mathlib.Analysis.SpecialFunctions.Artanh

namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

def noiseKernel {n : ℕ} (u : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then (1 + u) / 2 else (1 - u) / 2

def noiseOperator {n : ℕ} (u : ℝ) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ y, noiseKernel u x y * g y

abbrev flip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  LeanBlast.GotsmanLinial.flip i x

def cubeDerivative {n : ℕ} (i : Fin n) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  (g x - g (flip i x)) / 2

def psi (v : ℝ) : ℝ :=
  (1 + v) / 2 * Real.log (1 + v) + (1 - v) / 2 * Real.log (1 - v)

def entropy (v : ℝ) : ℝ := ell - psi v

def entropyAverage {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  cubeAverage (fun x => entropy (g x))

def informationDeficit {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  entropy (cubeAverage g) - entropyAverage g

def meanVariance {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  1 - (cubeAverage g) ^ 2

def dissipation {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  ∑ i, cubeAverage (fun x => Real.artanh (g x) * cubeDerivative i g x)

def IsInterior {n : ℕ} (g : Cube n → ℝ) : Prop :=
  ∀ x, -1 < g x ∧ g x < 1

def IsSignValued {n : ℕ} (g : Cube n → ℝ) : Prop :=
  ∀ x, g x = 1 ∨ g x = -1

def IsIncreasing {n : ℕ} (g : Cube n → ℝ) : Prop :=
  ∀ x y, (∀ i, x i ≤ y i) → g x ≤ g y

def signEncoding {n : ℕ} (f : Cube n → Bool) (x : Cube n) : ℝ :=
  if f x then 1 else -1

def restrict {n : ℕ} (g : Cube (n + 1) → ℝ) (b : Bool) (x : Cube n) : ℝ :=
  g (Fin.cases b x)

def pairMean {n : ℕ} (g : Cube (n + 1) → ℝ) (x : Cube n) : ℝ :=
  (restrict g true x + restrict g false x) / 2

def pairHalfDifference {n : ℕ} (g : Cube (n + 1) → ℝ) (x : Cube n) : ℝ :=
  (restrict g true x - restrict g false x) / 2

def pairEntropyGap (a b : ℝ) : ℝ :=
  entropy a - (entropy (a + b) + entropy (a - b)) / 2

def pairDissipation (a b : ℝ) : ℝ :=
  b / 2 * (Real.artanh (a + b) - Real.artanh (a - b))

end LeanBlast.CourtadeKumar

end

end OAI
