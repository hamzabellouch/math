import OAI.LinearAlgebra.MatrixMultiplication.Completion.RecursiveCompletion

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.RecursiveCompletion

open MatrixMultiplication.Foundation

inductive Script where
  | base
  | step (prior : Script) (center : Color) (size : ℕ)

namespace Script

def factors : Script → ℕ
  | .base => 1
  | .step prior _ m => prior.factors * m

def Coord (U : Type*) : Script → Type _
  | .base => U
  | .step prior _ m => Fin m → Coord U prior

instance coordFintype (U : Type*) [Fintype U] (s : Script) : Fintype (Coord U s) := by
  induction s with
  | base => exact inferInstanceAs (Fintype U)
  | step prior center m ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Fin m → Coord U prior))

def tensor {X Y Z : Type*} (S : FlaggedTensor X Y Z) :
    (s : Script) → FlaggedTensor (Coord X s) (Coord Y s) (Coord Z s)
  | .base => S
  | .step prior center m => complete (tensor S prior) center m

def order (d : ℕ) : Script → ℕ
  | .base => d
  | .step prior _ m => order d prior * m * 2 + 1

def degree (D : ℕ) : Script → ℕ
  | .base => D
  | .step prior _ m => degree D prior * m * 2 + 1 + 1 + 1

def approximation {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (S : FlaggedTensor X Y Z) {R d D : ℕ}
    (A : Tensor.PolynomialApproximation S.tensor R d D) (s : Script) :
    Tensor.PolynomialApproximation (tensor S s).tensor
      (R ^ s.factors) (order d s) (degree D s) := by
  induction s with
  | base => simpa only [tensor, Coord, factors, order, degree, pow_one] using A
  | step prior center m ih =>
      have next := (completionDegeneration (tensor S prior) center m).compose (ih.power m)
      simpa only [tensor, Coord, factors, order, degree, pow_mul] using next

theorem rank_power {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (S : FlaggedTensor X Y Z) {R d D : ℕ}
    (A : Tensor.PolynomialApproximation S.tensor R d D) (s : Script) (n : ℕ) :
    Tensor.RankAtMost (Tensor.power (tensor S s).tensor n)
      ((degree D s * n + 1) * (R ^ s.factors) ^ n) :=
  (approximation S A s).rank_power n

def dual : Script :=
  step (step (step (step (step (step (step base .B 2) .A 2) .C 2) .B 3) .C 2) .B 2) .A 3

def curve : Script := step base .A 3

def square : Script :=
  step (step (step (step (step base .B 2) .A 3) .C 2) .B 2) .A 3

@[simp] theorem dual_factors : dual.factors = 288 := by rfl
@[simp] theorem curve_factors : curve.factors = 3 := by rfl
@[simp] theorem square_factors : square.factors = 72 := by rfl

end Script
end MatrixMultiplication.RecursiveCompletion

end

end OAI
