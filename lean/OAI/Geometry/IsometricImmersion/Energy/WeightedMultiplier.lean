import OAI.Geometry.IsometricImmersion.Calculus.HessianCommutator
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def edgeDistance (b : ℝ) (p : Coord) : ℝ := b - p 1

def weightPhase (lambda : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  -lambda * p 1 + I p

def directedWeight (b lambda : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  (edgeDistance b p) ^ 8 * Real.exp (weightPhase lambda I p)

def directedM (b lambda : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  -directedWeight b lambda I p

def directedN (b lambda epsilon : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  epsilon * p 0 * directedWeight b lambda I p

def weightH0 (b lambda : ℝ) (p : Coord) : ℝ := lambda + 8 / edgeDistance b p

def multiplierT (B m n : Coord → ℝ) (p : Coord) : ℝ :=
  (coordPartial 1 m p - coordPartial 0 n p) / 2 + B p * n p

def multiplierS (A C m n : Coord → ℝ) (p : Coord) : ℝ :=
  -coordPartial 1 (fun q => A q * m q) p / 2 +
    coordPartial 0 (fun q => A q * n q) p / 2 + C p * m p

def multiplierJ (A B C m n : Coord → ℝ) (p : Coord) : ℝ :=
  -coordPartial 0 m p + B p * m p -
    coordPartial 1 (fun q => A q * n q) p + C p * n p

variable {I : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem directedWeight_differentiableAt
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    DifferentiableAt ℝ (directedWeight b lambda I) p := by
  have hD := (hasFDerivAt_const (𝕜 := ℝ) b p).sub (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hPhi := ((hasFDerivAt_apply (𝕜 := ℝ) 1 p).const_mul (-lambda)).add hI.hasFDerivAt
  have hd := (hD.pow 8).fun_mul hPhi.exp
  simp only [Pi.add_def, Pi.sub_def] at hd
  exact hd.differentiableAt

theorem directedWeight_partial
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) (i : Fin 2) :
    coordPartial i (directedWeight b lambda I) p =
      -8 * (edgeDistance b p) ^ 7 * (if (1 : Fin 2) = i then 1 else 0) *
          Real.exp (weightPhase lambda I p) +
        directedWeight b lambda I p *
          (coordPartial i I p - lambda * (if (1 : Fin 2) = i then 1 else 0)) := by
  have hD := (hasFDerivAt_const (𝕜 := ℝ) b p).sub (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hPhi := ((hasFDerivAt_apply (𝕜 := ℝ) 1 p).const_mul (-lambda)).add hI.hasFDerivAt
  have hd := (hD.pow 8).fun_mul hPhi.exp
  simp only [Pi.add_def, Pi.sub_def] at hd
  change fderiv ℝ (fun q : Coord => (b - q 1) ^ 8 * Real.exp (-lambda * q 1 + I q))
    p (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;>
    simp [edgeDistance, directedWeight, weightPhase, coordPartial] <;> ring

theorem directedWeight_partial_t
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    coordPartial 0 (directedWeight b lambda I) p =
      directedWeight b lambda I p * coordPartial 0 I p := by
  simpa using directedWeight_partial b lambda hI 0

theorem directedWeight_partial_s
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    coordPartial 1 (directedWeight b lambda I) p =
      -8 * (edgeDistance b p) ^ 7 * Real.exp (weightPhase lambda I p) +
        directedWeight b lambda I p * (coordPartial 1 I p - lambda) := by
  simpa using directedWeight_partial b lambda hI 1

theorem directedWeight_partial_s_factored
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) (hd : edgeDistance b p ≠ 0) :
    coordPartial 1 (directedWeight b lambda I) p =
      directedWeight b lambda I p * (-weightH0 b lambda p + coordPartial 1 I p) := by
  rw [directedWeight_partial_s b lambda hI]
  unfold directedWeight weightH0
  field_simp [hd]
  ring

theorem directedWeight_contDiffOn (b lambda : ℝ) (hI : ContDiffOn ℝ ∞ I U) :
    ContDiffOn ℝ ∞ (directedWeight b lambda I) U := by
  have hy : ContDiffOn ℝ ∞ (fun p : Coord => p 1) U :=
    contDiffOn_apply ℝ ℝ 1 U
  have hD : ContDiffOn ℝ ∞ (fun p : Coord => b - p 1) U :=
    contDiffOn_const.sub hy
  have hLambda : ContDiffOn ℝ ∞ (fun _ : Coord => -lambda) U := contDiffOn_const
  have hPhi : ContDiffOn ℝ ∞ (fun p : Coord => -lambda * p 1 + I p) U :=
    (hLambda.mul hy).add hI
  exact (hD.pow 8).mul hPhi.exp

theorem directedWeight_pos (b lambda : ℝ) (I : Coord → ℝ) (p : Coord) (hp : p 1 < b) :
    0 < directedWeight b lambda I p :=
  mul_pos (pow_pos (sub_pos.mpr hp) 8) (Real.exp_pos _)

theorem directedWeight_edge_zero (b lambda : ℝ) (I : Coord → ℝ) (p : Coord)
    (hp : p 1 = b) : directedWeight b lambda I p = 0 := by
  simp [directedWeight, edgeDistance, hp]

theorem directedWeight_partial_edge_zero
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) (hp : p 1 = b) (i : Fin 2) :
    coordPartial i (directedWeight b lambda I) p = 0 := by
  rw [directedWeight_partial b lambda hI i]
  simp [edgeDistance, directedWeight, hp]

theorem directedM_differentiableAt
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    DifferentiableAt ℝ (directedM b lambda I) p :=
  (directedWeight_differentiableAt b lambda hI).neg

theorem directedN_differentiableAt
    (b lambda epsilon : ℝ) (hI : DifferentiableAt ℝ I p) :
    DifferentiableAt ℝ (directedN b lambda epsilon I) p :=
  ((differentiableAt_apply (𝕜 := ℝ) 0 p).const_mul epsilon).mul
    (directedWeight_differentiableAt b lambda hI)

theorem directedM_partial (b lambda : ℝ) (i : Fin 2) :
    coordPartial i (directedM b lambda I) p =
      -coordPartial i (directedWeight b lambda I) p := by
  change fderiv ℝ (fun q : Coord => -directedWeight b lambda I q) p (Pi.single i 1) =
    -fderiv ℝ (directedWeight b lambda I) p (Pi.single i 1)
  simp only [fderiv_fun_neg, neg_apply]

theorem directedN_partial
    (b lambda epsilon : ℝ) (hI : DifferentiableAt ℝ I p) (i : Fin 2) :
    coordPartial i (directedN b lambda epsilon I) p =
      epsilon * (if (0 : Fin 2) = i then 1 else 0) * directedWeight b lambda I p +
        epsilon * p 0 * coordPartial i (directedWeight b lambda I) p := by
  have hd := ((hasFDerivAt_apply (𝕜 := ℝ) 0 p).const_mul epsilon).fun_mul
    (directedWeight_differentiableAt b lambda hI).hasFDerivAt
  change fderiv ℝ (fun q : Coord => epsilon * q 0 * directedWeight b lambda I q)
    p (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;> simp [coordPartial]
  ring

theorem directed_mn_edge_zero
    (b lambda epsilon : ℝ) (I : Coord → ℝ) (p : Coord) (hp : p 1 = b) :
    directedM b lambda I p = 0 ∧ directedN b lambda epsilon I p = 0 := by
  simp [directedM, directedN, directedWeight_edge_zero b lambda I p hp]

theorem directed_coefficients
    (A B C : Coord → ℝ) (b lambda epsilon : ℝ)
    (hA : DifferentiableAt ℝ A p) (hI : DifferentiableAt ℝ I p)
    (hd : edgeDistance b p ≠ 0) :
    multiplierT B (directedM b lambda I) (directedN b lambda epsilon I) p =
      directedWeight b lambda I p *
        ((weightH0 b lambda p - coordPartial 1 I p - epsilon +
          epsilon * p 0 * (2 * B p - coordPartial 0 I p)) / 2) ∧
    multiplierS A C (directedM b lambda I) (directedN b lambda epsilon I) p =
      directedWeight b lambda I p *
        (coordPartial 1 A p / 2 - weightH0 b lambda p * A p / 2 +
          epsilon * p 0 * coordPartial 0 A p / 2 - C p +
          A p * (coordPartial 1 I p + epsilon + epsilon * p 0 * coordPartial 0 I p) / 2) ∧
    multiplierJ A B C (directedM b lambda I) (directedN b lambda epsilon I) p =
      directedWeight b lambda I p *
        (coordPartial 0 I p - B p + epsilon * p 0 *
          (C p - coordPartial 1 A p + A p * (weightH0 b lambda p - coordPartial 1 I p))) := by
  have hm := directedM_differentiableAt b lambda hI
  have hn := directedN_differentiableAt b lambda epsilon hI
  have hwt := directedWeight_partial_t b lambda hI
  have hws := directedWeight_partial_s_factored b lambda hI hd
  constructor
  · unfold multiplierT
    rw [directedM_partial, directedN_partial b lambda epsilon hI]
    simp only [Fin.isValue, ↓reduceIte, mul_one, hwt, hws, directedN]
    ring
  constructor
  · unfold multiplierS
    rw [HessianCalculus.coordPartial_mul_at hA hm 1,
      HessianCalculus.coordPartial_mul_at hA hn 0,
      directedM_partial, directedN_partial b lambda epsilon hI]
    simp only [Fin.isValue, ↓reduceIte, mul_one, hwt, hws, directedM, directedN]
    ring
  · unfold multiplierJ
    rw [HessianCalculus.coordPartial_mul_at hA hn 1,
      directedM_partial, directedN_partial b lambda epsilon hI]
    have h01 : ¬((0 : Fin 2) = 1) := by decide
    simp only [Fin.isValue, h01, ↓reduceIte, mul_zero, zero_mul, zero_add,
      hwt, hws, directedM, directedN]
    ring

theorem directedS_transverse_expansion
    (A B C : Coord → ℝ) (b lambda epsilon : ℝ) (ell : ℕ) (r : ℝ)
    (hA : DifferentiableAt ℝ A p) (hI : DifferentiableAt ℝ I p)
    (hd : edgeDistance b p ≠ 0)
    (hC : C p = ((ell : ℝ) + 1) * coordPartial 1 A p + A p * r) :
    multiplierS A C (directedM b lambda I) (directedN b lambda epsilon I) p =
      directedWeight b lambda I p *
        (-((ell : ℝ) + 1 / 2) * coordPartial 1 A p +
          epsilon * p 0 * coordPartial 0 A p / 2 - weightH0 b lambda p * A p / 2 +
          A p * ((coordPartial 1 I p + epsilon + epsilon * p 0 * coordPartial 0 I p) / 2 - r)) := by
  rw [(directed_coefficients A B C b lambda epsilon hA hI hd).2.1, hC]
  ring

end SmoothLocal.Weighted

end

end OAI
