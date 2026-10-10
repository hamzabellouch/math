import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import OAI.Geometry.NodalSets.Coefficients.CorrectionAlgebra

namespace OAI

namespace Yau
noncomputable section
variable {n : ℕ}
abbrev Coord (n : ℕ) := Fin n → ℝ

def coordPartial (u : Coord n → ℝ) (x : Coord n) (i : Fin n) : ℝ :=
  fderiv ℝ u x (Pi.single i 1)

def coordDiv (V : Coord n → Coord n) (x : Coord n) : ℝ :=
  ∑ i, coordPartial (fun y ↦ V y i) x i

def weightedDiv (gamma : Coord n → ℝ) (V : Coord n → Coord n)
    (x : Coord n) : ℝ :=
  (gamma x)⁻¹ * coordDiv (fun y i ↦ gamma y * V y i) x

def pairing (u : Coord n → ℝ) (V : Coord n → Coord n) (x : Coord n) : ℝ :=
  ∑ i, coordPartial u x i * V x i

theorem coordDiv_mul {u : Coord n → ℝ} {V : Coord n → Coord n} {x : Coord n}
    (hu : DifferentiableAt ℝ u x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y ↦ V y i) x) :
    coordDiv (fun y i ↦ u y * V y i) x =
      u x * coordDiv V x + pairing u V x := by
  unfold coordDiv pairing coordPartial
  simp_rw [fderiv_fun_mul hu (hV _)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weightedDiv_mul {gamma u : Coord n → ℝ} {V : Coord n → Coord n}
    {x : Coord n} (hg : DifferentiableAt ℝ gamma x) (hgn : gamma x ≠ 0)
    (hu : DifferentiableAt ℝ u x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y ↦ V y i) x) :
    weightedDiv gamma (fun y i ↦ u y * V y i) x =
      u x * weightedDiv gamma V x + pairing u V x := by
  have heq : (fun y i ↦ gamma y * (u y * V y i)) =
      (fun y i ↦ u y * (gamma y * V y i)) := by
    funext y i
    ring
  unfold weightedDiv
  rw [heq, coordDiv_mul (V := fun y i ↦ gamma y * V y i) hu (fun i ↦ hg.mul (hV i))]
  have hp : pairing u (fun y i ↦ gamma y * V y i) x = gamma x * pairing u V x := by
    unfold pairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hp]
  field_simp

theorem weighted_exact_correction {gamma u f : Coord n → ℝ}
    {V : Coord n → Coord n} {x : Coord n} {lam residual : ℝ}
    (hg : DifferentiableAt ℝ gamma x) (hgn : gamma x ≠ 0)
    (hu : DifferentiableAt ℝ u x) (hf : DifferentiableAt ℝ f x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y ↦ V y i) x)
    (hlam : lam ≠ 0) (hden : pairing u V x + lam * u x ^ 2 ≠ 0)
    (hfval : f x = residual / (pairing u V x + lam * u x ^ 2)) :
    weightedDiv gamma (fun y i ↦ u y * (f y * V y i)) x +
      lam * (f x * u x - lam⁻¹ *
        weightedDiv gamma (fun y i ↦ f y * V y i) x) * u x = residual := by
  rw [weightedDiv_mul (V := fun y i ↦ f y * V y i) hg hgn hu (fun i ↦ hf.mul (hV i))]
  have hp : pairing u (fun y i ↦ f y * V y i) x = f x * pairing u V x := by
    unfold pairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hp, hfval]
  exact exact_correction hlam hden

end
end Yau

end OAI
