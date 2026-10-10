import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.IsolatedSpectrum

namespace OAI

/-!
# Minimal published hydrogen input for isolated-well energies

Gerald Teschl, *Mathematical Methods in Quantum Mechanics*, second edition,
AMS Graduate Studies in Mathematics 157 (2014), Theorem 10.10, equations
(10.5) and (10.64): the lowest eigenvalue of `-Δ-γ/|x|` is `-γ²/4`.
Set `γ=2`, divide the operator by two, and translate the centre. The exact
specialization used below is `PublishedHydrogenBottom`. Spin contributes two
identical summands and does not alter the bottom.
https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe2.pdf .

This conditional interface assumes the unperturbed hydrogen bottom.
The isolated-well comparison follows by a variational perturbation argument.
-/

noncomputable section
namespace ContinuumCoulomb

/-- Exact published hydrogen bottom, specialized to the unperturbed well. -/
def PublishedHydrogenBottom : Prop :=
  ∀ a : Position, hydrogenEnergy a = ((-1 / 2 : ℝ) : EReal)

theorem isolatedWellEnergy_near_hydrogen (hhydrogen : PublishedHydrogenBottom)
    {m : ℕ} {D q q' epsilon : ℝ}
    (hD : 128 ≤ D) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hq' : 0 ≤ q') (hq'1 : q' ≤ 1)
    (hprimary : |1 - q| ≤ epsilon) (hsecondary : q' ≤ epsilon)
    (hbackground : 48 * m / D ≤ epsilon) (hsmall : 10 * epsilon ≤ 1)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) :
    |(isolatedWellEnergy D q q' center displacement site).toReal + 1 / 2| ≤
      45 * epsilon := by
  have h := isolatedWellEnergy_relative hD hq hq1 hq' hq'1 hprimary hsecondary hbackground
    hsmall center displacement hdisp site
  rw [hhydrogen (center site), EReal.toReal_coe] at h
  calc
    _ = |(isolatedWellEnergy D q q' center displacement site).toReal - (-1 / 2)| := by
      congr 1
      ring
    _ ≤ 10 * epsilon * ((-1 / 2 : ℝ) + 5) := h
    _ = _ := by ring

/-- The actual rationally computed integer charges give the required uniform
energy closeness throughout the displacement cube, conditionally only on the
published unperturbed hydrogen bottom. -/
theorem binary_isolatedWellEnergy_bound (hhydrogen : PublishedHydrogenBottom)
    {D m : ℕ} (hm : 0 < m) (hscale : 10010 * m ≤ D)
    (center displacement : Fin m → Position) (hdisp : ∀ j, ‖displacement j‖ ≤ 4)
    (site : Fin m) :
    |(isolatedWellEnergy D (binaryPrimaryRatio D m) (binarySecondaryRatio D m)
      center displacement site).toReal + 1 / 2| ≤ 45045 * m / (D : ℝ) := by
  have hscale' : 2002 * m ≤ D := by omega
  have h := binaryWellCharges_spec hm hscale'
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hDlarge : (10010 : ℝ) * m ≤ D := by exact_mod_cast hscale
  have hD : (0 : ℝ) < D := by linarith
  have hr : 0 ≤ (m : ℝ) / D := by positivity
  have hs0 : 0 ≤ binarySecondaryRatio D m :=
    (by positivity : (0 : ℝ) ≤ 999 * m / D).trans h.2.2.2.2.2.1
  have hsmall : 10 * (1001 * m / (D : ℝ)) ≤ 1 := by
    have h : (10010 : ℝ) * m / D ≤ 1 := (div_le_iff₀ hD).mpr (by linarith)
    convert h using 1
    ring
  have hprimary : |1 - binaryPrimaryRatio D m| ≤ 1001 * m / (D : ℝ) := by
    apply h.2.2.2.2.1.trans
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_right (by norm_num : (501 : ℝ) ≤ 1001) hr
  have hbackground : 48 * m / (D : ℝ) ≤ 1001 * m / D := by
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_right (by norm_num : (48 : ℝ) ≤ 1001) hr
  have hbound := isolatedWellEnergy_near_hydrogen hhydrogen
    (by linarith : (128 : ℝ) ≤ D) h.2.2.1 h.2.2.2.1 hs0 h.2.2.2.2.2.2.2
    hprimary h.2.2.2.2.2.2.1 hbackground hsmall center displacement hdisp site
  convert hbound using 1
  ring

end ContinuumCoulomb

end

end OAI
