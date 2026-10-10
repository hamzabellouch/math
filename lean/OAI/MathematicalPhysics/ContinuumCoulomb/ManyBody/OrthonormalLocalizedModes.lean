import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.GramCorrection
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedLinearOrbitals
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RealSpinOrbitals

namespace OAI

/-! The actual spectral inverse-square-root correction applied to the
manufactured orbitals. These are C1 decaying orthonormal spatial functions;
injectively occupied spatial/spin modes give actual normalized fermions. -/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace ContinuumCoulomb

def localizedModeGram {m : ℕ} (u : Fin m → PlanarPosition) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => planarModeOverlap (u i) (u j)

theorem localizedModeGram_isHermitian {m : ℕ} (u : Fin m → PlanarPosition) :
    (localizedModeGram u).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  change planarModeOverlap (u j) (u i) = planarModeOverlap (u i) (u j)
  unfold planarModeOverlap
  apply integral_congr_ae
  filter_upwards [] with r
  exact mul_comm _ _

def correctedLocalizedCoefficients {m : ℕ} (u : Fin m → PlanarPosition) : Matrix (Fin m) (Fin m) ℝ :=
  GramCorrection.correction (localizedModeGram_isHermitian u)

def correctedLocalizedMode (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) : Position → ℝ :=
  localizedLinearOrbital freq u (correctedLocalizedCoefficients u i)

theorem correctedLocalizedCoefficients_gram {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m * localizedOverlapBound D ≤ 1/2) :
    correctedLocalizedCoefficients u * localizedModeGram u * (correctedLocalizedCoefficients u)ᵀ = 1 := by
  have hpos (i : Fin m) : 0 < (localizedModeGram_isHermitian u).eigenvalues i := by
    have h := (GramCorrection.eigenvalue_bounds (localizedModeGram_isHermitian u)
      (localizedOverlapBound_nonnegative D) (fun j => planarModeOverlap_diagonal (u j))
      (planarModeOverlap_offsite u hsep) i).1
    linarith
  have h := GramCorrection.correction_gram (localizedModeGram_isHermitian u) hpos
  rw [GramCorrection.correction_transpose] at h
  simpa only [correctedLocalizedCoefficients, GramCorrection.correction_transpose] using h

theorem correctedLocalizedCoefficients_entries {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m * localizedOverlapBound D ≤ 1/2) (i j : Fin m) :
    |correctedLocalizedCoefficients u i j - if i=j then 1 else 0| ≤ 2*m*localizedOverlapBound D ∧
      |correctedLocalizedCoefficients u i j| ≤ 2 :=
  GramCorrection.correction_entry_bounds (localizedModeGram_isHermitian u)
    (localizedOverlapBound_nonnegative D) (fun j => planarModeOverlap_diagonal (u j))
    (planarModeOverlap_offsite u hsep) hs i j

theorem correctedLocalizedMode_inner {freq D : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m * localizedOverlapBound D ≤ 1/2) (i j : Fin m) :
    (∫ x, correctedLocalizedMode freq u i x * correctedLocalizedMode freq u j x) =
      if i=j then (1 : ℝ) else 0 := by
  rw [correctedLocalizedMode, correctedLocalizedMode, localizedLinearOrbital_inner hfreq]
  have he : (∑ p, ∑ q, (correctedLocalizedCoefficients u i p * correctedLocalizedCoefficients u j q) *
      planarModeOverlap (u p) (u q)) =
      (correctedLocalizedCoefficients u * localizedModeGram u * (correctedLocalizedCoefficients u)ᵀ) i j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, localizedModeGram]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [he, correctedLocalizedCoefficients_gram u hsep hs, Matrix.one_apply]

theorem correctedLocalizedMode_C1 (freq : ℝ) {m : ℕ} (u : Fin m → PlanarPosition) (i : Fin m) :
    ContDiff ℝ 1 (correctedLocalizedMode freq u i) :=
  (localizedLinearOrbital_C7 freq u _).of_le (by norm_num)

theorem correctedLocalizedMode_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) : MemLp (correctedLocalizedMode freq u i) 2 :=
  localizedLinearOrbital_memLp hfreq u _

theorem correctedLocalizedMode_partial_memLp {freq : ℝ} (hfreq : 0 < freq) {m : ℕ}
    (u : Fin m → PlanarPosition) (i : Fin m) (b : Fin 3) :
    MemLp (fun x => fderiv ℝ (correctedLocalizedMode freq u i) x (EuclideanSpace.single b 1)) 2 :=
  localizedLinearOrbital_fderiv_memLp hfreq u _ _

def correctedLocalizedSlaterState {freq : ℝ} (hfreq : 0 < freq) {m n : ℕ}
    (u : Fin m → PlanarPosition) (p : Fin n → Fin m × Fin 2) : Coulomb.H1Vector n :=
  selectedRealSlaterState (correctedLocalizedMode freq u) (correctedLocalizedMode_C1 freq u)
    (correctedLocalizedMode_memLp hfreq u) (correctedLocalizedMode_partial_memLp hfreq u) p

theorem correctedLocalizedSlaterState_antisymmetric {freq : ℝ} (hfreq : 0 < freq) {m n : ℕ}
    (u : Fin m → PlanarPosition) (p : Fin n → Fin m × Fin 2) :
    Coulomb.Antisymmetric (correctedLocalizedSlaterState hfreq u p) :=
  selectedRealSlaterState_antisymmetric _ _ _ _ _

theorem correctedLocalizedSlaterState_normalized {freq D : ℝ} (hfreq : 0 < freq) {m n : ℕ}
    (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m * localizedOverlapBound D ≤ 1/2) (p : Fin n → Fin m × Fin 2) (hp : Function.Injective p) :
    Coulomb.mass (correctedLocalizedSlaterState hfreq u p) = 1 :=
  selectedRealSlaterState_normalized _ _ _ _ (fun i j => by
    by_cases hij : i=j
    · simpa only [hij, ite_true] using correctedLocalizedMode_inner hfreq u hsep hs i j
    · simpa only [hij, ite_false] using correctedLocalizedMode_inner hfreq u hsep hs i j) p hp

end ContinuumCoulomb

end

end OAI
