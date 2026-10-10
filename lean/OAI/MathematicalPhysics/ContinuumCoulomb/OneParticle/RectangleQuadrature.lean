import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.UniformSamplesOn

namespace OAI

/-! Quantitative tensor quadrature in two coordinates, with independent
coordinate moduli and errors in each computed sample. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.UniformQuadrature

theorem node_mem {a h : ℝ} {N i : ℕ} (hh : 0 ≤ h) (hi : i ≤ N) :
    node a h i ∈ Set.Icc a (node a h N) := by
  constructor
  · dsimp only [node]
    linarith [mul_nonneg (Nat.cast_nonneg i) hh]
  · dsimp only [node]
    exact add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh) a

def rectangleSum (hx hy : ℝ) (Nx Ny : ℕ) (v : ℕ → ℕ → ℝ) : ℝ :=
  sampleSum hx Nx (fun i => sampleSum hy Ny (v i))

theorem rectangle_error (f : ℝ → ℝ → ℝ) (v : ℕ → ℕ → ℝ)
    (a hx : ℝ) (Nx : ℕ) (b hy : ℝ) (Ny : ℕ) {Lx Ly ε : ℝ}
    (hhx : 0 ≤ hx) (hhy : 0 ≤ hy) (hLx : 0 ≤ Lx) (hLy : 0 ≤ Ly)
    (hLipX : ∀ x ∈ Set.Icc a (node a hx Nx), ∀ x' ∈ Set.Icc a (node a hx Nx),
      ∀ y ∈ Set.Icc b (node b hy Ny), |f x y - f x' y| ≤ Lx * |x - x'|)
    (hLipY : ∀ x ∈ Set.Icc a (node a hx Nx), ∀ y ∈ Set.Icc b (node b hy Ny),
      ∀ y' ∈ Set.Icc b (node b hy Ny), |f x y - f x y'| ≤ Ly * |y - y'|)
    (heval : ∀ i < Nx, ∀ j < Ny,
      |v i j - f (node a hx i) (node b hy j)| ≤ ε) :
    |rectangleSum hx hy Nx Ny v -
      ∫ x in a..node a hx Nx, ∫ y in b..node b hy Ny, f x y| ≤
      ((Nx : ℝ) * hx) * ((Ny : ℝ) * hy) * (Lx * hx + Ly * hy + ε) := by
  have hylen : node b hy Ny - b = (Ny : ℝ) * hy := by dsimp [node]; ring
  have hys : b ≤ node b hy Ny := (node_mem hhy (Nat.le_refl Ny)).1
  have hL : 0 ≤ ((Ny : ℝ) * hy) * Lx := by positivity
  have hsection : ∀ x ∈ Set.Icc a (node a hx Nx),
      ContinuousOn (f x) (Set.Icc b (node b hy Ny)) := by
    intro x hx'
    exact continuousOn_of_abs_sub_le (hLipY x hx')
  have houterLip : ∀ x ∈ Set.Icc a (node a hx Nx),
      ∀ x' ∈ Set.Icc a (node a hx Nx),
      |(∫ y in b..node b hy Ny, f x y) - ∫ y in b..node b hy Ny, f x' y| ≤
        (((Ny : ℝ) * hy) * Lx) * |x - x'| := by
    intro x hx' x' hx''
    have h := integral_parameter_lipschitz f hys hsection hLipX hx' hx''
    simpa only [hylen] using h
  have hinner : ∀ i < Nx,
      |sampleSum hy Ny (v i) - ∫ y in b..node b hy Ny, f (node a hx i) y| ≤
        ((Ny : ℝ) * hy) * (Ly * hy + ε) := by
    intro i hi
    have h := samples_error_lipschitz (f (node a hx i)) (v i) b hy Ny hhy hLy
      (hLipY (node a hx i) (node_mem hhx hi.le)) (heval i hi)
    convert h using 1
    ring
  have h := samples_error_lipschitz (fun x => ∫ y in b..node b hy Ny, f x y)
    (fun i => sampleSum hy Ny (v i)) a hx Nx hhx hL houterLip hinner
  change |rectangleSum hx hy Nx Ny v - _| ≤ _ at h
  convert h using 1
  ring

end ContinuumCoulomb.UniformQuadrature

end

end OAI
