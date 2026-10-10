import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedOrbitalResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.OrthonormalLocalizedModes

namespace OAI

/-! Gram correction preserves a polynomial residual bound: it sums over
spatial modes, independently of the many-electron occupation basis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def correctedManufacturedResidual (rho H S freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (x : Position) : ℝ :=
  ∑ j, correctedLocalizedCoefficients u i j*manufacturedOrbitalResidual rho H S freq scale u j x

theorem correctedManufacturedResidual_memLp {rho H S freq : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hfreq : 0 < freq)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcoeff : ∀ j, 0 ≤ localizedCounterterm freq u j/scale ∧
      localizedCounterterm freq u j/scale ≤ δ) (i : Fin m) :
    MemLp (correctedManufacturedResidual rho H S freq scale u i) 2 :=
  memLp_finsetSum Finset.univ (fun j _ =>
    (manufacturedOrbitalResidual_memLp hrho hH hS hfreq scale u hδ hcoeff j).const_mul _)

theorem correctedManufacturedResidual_square_bound {rho H S freq δ D R : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (hδ : 0 ≤ δ)
    (hcoeff : ∀ j, 0 ≤ localizedCounterterm freq u j/scale ∧
      localizedCounterterm freq u j/scale ≤ δ) (i : Fin m) :
    (∫ x, correctedManufacturedResidual rho H S freq scale u i x^2) ≤
      4*(m : ℝ)*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D R u j) := by
  have hraw (j : Fin m) :=
    manufacturedOrbitalResidual_square_integrable hrho hH.le hS.le hfreq scale u hδ hcoeff j
  have hc (j : Fin m) : correctedLocalizedCoefficients u i j^2 ≤ 4 := by
    have h := (correctedLocalizedCoefficients_entries u hsep hs i j).2
    calc
      _ = |correctedLocalizedCoefficients u i j|^2 := (sq_abs _).symm
      _ ≤ (2:ℝ)^2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = 4 := by norm_num
  have hpoint (x : Position) : correctedManufacturedResidual rho H S freq scale u i x^2 ≤
      4*(m : ℝ)*(∑ j, manufacturedOrbitalResidual rho H S freq scale u j x^2) := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j => correctedLocalizedCoefficients u i j*manufacturedOrbitalResidual rho H S freq scale u j x)
    simp only [Finset.card_univ,Fintype.card_fin] at h
    change correctedManufacturedResidual rho H S freq scale u i x^2 ≤ _ at h
    apply h.trans
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_right (hc j) (sq_nonneg (manufacturedOrbitalResidual rho H S freq scale u j x)))
    simp only [mul_pow] at *
    have hmul := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    calc
      _ ≤ (m:ℝ)*(∑ j, 4*manufacturedOrbitalResidual rho H S freq scale u j x^2) := hmul
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hi := integral_mono
    (correctedManufacturedResidual_memLp hrho hH.le hS.le hfreq scale u hδ hcoeff i).integrable_sq
    ((integrable_finsetSum Finset.univ (fun j _ => hraw j)).const_mul (4*(m:ℝ))) hpoint
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ => hraw j)] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ =>
    manufacturedOrbitalResidual_square_bound hrho hH hS hfreq hR hRH hRS scale u hsep hδ hcoeff j))
    (by positivity))

end ContinuumCoulomb

end

end OAI
